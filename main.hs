{-|
 _____   _     _   __   __   _____   _       ______  _____   ______  ______ 
(_____) (_)   (_) (__)_(__) (_____) (_)     (______)(_____) (______)(______)
(_)__(_)(_)   (_)(_) (_) (_)(_)__(_)(_)     (_)__   (_)__(_)(_)__   (_)__   
(_____) (_)   (_)(_) (_) (_)(_____) (_)     (____)  (_____) (____)  (____)  
(_)__(_)(_)___(_)(_)     (_)(_)__(_)(_)____ (_)____ (_)__(_)(_)____ (_)____ 
(_____)  (_____) (_)     (_)(_____) (______)(______)(_____) (______)(______)
                                                                            
-}

-- Monad transforms are very useful for parsing, most commonly associated with language interpreters. 
-- Thanks to Transformers and the integration of Monadic Programming, it's possible to implement 
-- custom monads by utilising Monad Transformers.

-- For example, below highlights a small interpreter for a simple programming language.

module Main where

import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

-- For dealing with optional Values
import Data.Maybe

-- Defines Finite Maps
import qualified Data.Map as Map 

-- Data Types to define Environments (variable-value mappings):

-- 'Name' for Variable Names:
type Name = String 

-- 'Exp' with variants:
data Exp = Literal Integer -- Literal
         | Var Name -- Variable Name
         | Plus Exp Exp -- Addition
         | Sub Exp Exp -- Subtraction
         | Lambda Name Exp -- Lambda Exp
         | App Exp Exp -- Applicative Rule
         deriving (Show)

-- Define 'Value' with variants. The 'FuncVal' is a type for functions as the 'Value' type is either
--  Integers or Functions (Closures):
data Value = IntVal Integer
           | FuncVal Env Name Exp
           deriving (Show)

-- 'Env' for envionment that Maps Names to Values:
type Env = Map.Map Name Value

-- Furthermore, a 'Reference Implementation' of the interpreter using an evaluation function is defined.
-- Integers simply evaluate to themselves as handled using the data 'Value' type to which they are bounded
-- to some envionment. The 'fromJust' function is declared here because 'Map.lookup' returns a 'Maybe' 
-- value, so values that are optional can be handled. The 'let...in and case...of' expression for Lambda 
-- delegates an error rule, for any variable not bounded not using Lambda Expressions that intends Lambda. 
-- Addition for 'Plus' is evaluated by two operands and their sum.

parse' :: Env -> Exp -> Value
parse' env (Literal i)  = IntVal i
parse' env (Var n)      = fromJust (Map.lookup n env)
parse' env (Plus e1 e2) = let IntVal i1 = parse' env e1
                              IntVal i2 = parse' env e2
                          in  IntVal (i1 + i2)
parse' env (Sub e1 e2) = let IntVal i1 = parse' env e1
                             IntVal i2 = parse' env e2
                          in IntVal (i1 - i2)
parse' env (Lambda n e)  = FuncVal env n e
parse' env (App e1 e2)  = let val1 = parse' env e1
                              val2 = parse' env e2
                          in case val1 of
                            FuncVal env' n body -> parse' (Map.insert n val2 env') body 


-- Use case: 42 + ((\x -> x)(6 + 10) ->
-- Using the following expression, when returing the following:
-- parse' Map.empty exExp -> IntVal 58
exExp = Literal 42 `Plus`(App(Lambda "x" (Var "x"))(Literal 6 `Plus` Literal 10))
-- Use case: 20 - ((\i -> i)(10 + 5) ->
-- Using the following expression, when returing the following:
-- parse0 Map.empty exExp' -> IntVal 5
exExp' = Literal 20 `Sub` (App(Lambda "i" (Var "i"))(Literal 10 `Plus` Literal 5)) 

-- However, this all well and good but Monad Transformers can offer more control and flexibility when
-- it comes to interpreters thanks to Monadic operations using 'do' notation.

-- First define a new evaluation function using Monadic operation.
-- Create a Type Synonym as Eval' ά -> Identity ά. 'Identity' is a Monad being imported from our 
--declaration above 'Control.Monad.Identity' that constructs return operations for all procedures in 
-- the Monad. The 'RunIdentity' function is used to do just that.

type Eval' expr = Identity expr

-- Set up a function 'runEval1' to simply call the 'runIdentity' function.
runEval' :: Eval' expr -> expr
runEval' ev     =  runIdentity ev

-- Assuming the Eval1 ά Monad assignment to 'Identity' is in place, the 'parse'' function can be 
-- reimposed as using 'do' notation and returning '$' functions specifying a result.

eval' :: Env -> Exp -> Eval' Value
eval' env (Literal i)   = return $ IntVal i
eval' env (Var n)       = return $ fromJust $ Map.lookup n env
eval' env (Plus e1 e2)  = do IntVal i1 <- eval' env e1
                             IntVal i2 <- eval' env e2
                             return $ IntVal (i1 + i2)
eval' env (Sub e1 e2)  = do IntVal i1 <- eval' env e1
                            IntVal i2 <- eval' env e2
                            return $ IntVal (i1 - i2)
eval' env (Lambda n e)   = return $ FuncVal env n e
eval' env (App e1 e2)   = do val1 <- eval' env e1
                             val2 <- eval' env e2
                             case val1 of
                               FuncVal env' n body ->
                                  eval' (Map.insert n val2 env') body
 
-- Now when running the command 'eval' Map.empty exExp' we should see the result 'IntVal 58'. 
-- Notice the removal of 'RunEval' (...)' and our handler in parenthesis?

-- Therefore, to turn programs into more Monadic structures we need to simply return '$' 
-- function results and return Monadic actions using 'do' notation. 

-- Monad is a Monad if its type is a Monad Class whereby we implement the notation for return '$' 
-- and 'do, case, of' or (>>=) to create more semantic behaviour for the type internally.

-- Using a Monad from the library there can be more robust exception handling put in place using 
-- 'ExceptT' to delegate a Type for Error. Using 'String' in the type signature means the values 
-- used can be checked based on the ErrorT conditions. There could be more done here though, 'String'
-- could be changed into source locations etc.

type EvalError expr = ExceptT String Identity expr

runEvalError :: EvalError expr -> Either String expr
runEvalError env = runIdentity (runExceptT env)

parser :: Env -> Exp -> runEvalError Value
parser env (Literal i)  = return $ IntVal i
parser env (Var n)      = return $ fromJust $ Map.lookup n env
parser env (Plus e1 e2) = do
                            e1' <- parser env e1
                            e2' <- parser env e2
                            case (e1', e2') of 
                                (IntVal i1, IntVal i2) -> 
                                    return $ IntVal (i1 + i2)
                                _ ->
                                    throwError "type error in Plus"
parser env (Sub e1 e2) = do
                            e1' <- parser env e1
                            e2' <- parser env e2
                            case (e1', e2') of 
                                (IntVal i1, IntVal i2) -> 
                                    return $ IntVal (i1 - i2)
                                _ ->
                                    throwError "type error in Subtraction"
parser env (Lambda n e)  = return $ FuncVal env n e
parser env (App e1 e2) =  do val1 <- parser env e1
                             val2 <- parser env e2
                             case val1 of
                               FuncVal env' n body ->
                                parser (Map.insert n val2 env') body
                                
-- Here, some simple type checking can be executed using the following command 
-- 'parse (parse Map:empty (Plus (Literal 1) (Lambda "x" (Var"x"))))' and this should return 
-- an error and 'Control.Monad.Except' module should return specifics. 
