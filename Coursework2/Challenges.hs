-- COMP2209 Coursework 2, University of Southampton 2018
-- DUMMY FILE FOR YOU TO EDIT AND ADD YOUR OWN IMPLEMENTATIONS
-- NOTE THAT NO THIRD PARTY MODULES MAY BE USED IN SOLVING THESE EXERCISES AND
-- THAT YOU MAY NOT CHANGE THE FUNCTION TYPE SIGNATURES NOR TYPE DEFINITIONS
-- This module statement makes public only the specified functions and types
-- DO NOT CHANGE THIS LIST OF EXPORTED FUNCTIONS AND TYPES
module Challenges (convertLet, prettyPrint, parseLet, countReds, compileArith,
    Expr(App, Let, Var), LamExpr(LamApp, LamAbs, LamVar)) where

import Data.Char
import Parsing

-- Challenge 1
data Expr = App Expr Expr | Let [Int] Expr Expr | Var Int deriving (Show,Eq)
data LamExpr = LamApp LamExpr LamExpr | LamAbs Int LamExpr | LamVar Int deriving (Show,Eq)

-- convert a let expression to lambda expression
convertLet :: Expr -> LamExpr
--base case
convertLet (Var x) = LamVar x

convertLet (App e1 e2) = LamApp (convertLet(e1)) (convertLet(e2))

convertLet (Let [x] e1 e2) = LamApp(LamAbs x (convertLet e2)) (convertLet e1)

convertLet (Let (x:xs) (e1) (e2)) = LamApp (LamAbs (x) (convertLet e2)) (helper xs e1)

--a helper function that produces a lambda expression
helper :: [Int] -> Expr -> LamExpr
helper [x] (e) = LamAbs x (convertLet e)
helper (x:xs) e = LamAbs (x) (helper xs e)

-- Challenge 2
-- pretty print a let expression by converting it to a string
prettyPrint :: Expr -> String
prettyPrint (Var x) = "x" ++ show(x)
prettyPrint (App e1 e2) | isLet(e1) && not(isApp(e2)) = "(" ++ prettyPrint(e1) ++ ") " ++ prettyPrint(e2) -- put brackets on let expression
                        | isLet(e1) && isApp(e2) = "(" ++ prettyPrint(e1) ++ ") (" ++ prettyPrint(e2) ++ ")" -- put brackets on let expression and on application of application
                        | isApp(e2) = prettyPrint(e1) ++ " (" ++ prettyPrint(e2) ++ ")" -- put brackets if the second expression is application
                        | otherwise = prettyPrint(e1) ++ " " ++ prettyPrint(e2)
prettyPrint (Let (xs) e1 e2) = "let " ++ printList (xs) ++ "= " ++ prettyPrint(e1) ++ " in " ++ prettyPrint(e2)

printList :: [Int] -> String
printList [] = ""
printList (x:xs) = "x" ++ show(x) ++ " " ++ printList xs

--check if an expression is a let expression in particular
isLet :: Expr -> Bool
isLet (Let _ _ _) = True
isLet _ = False

--check if an expression is an application in particular
isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

-- Challenge 3
-- parse a let expression
parseLet :: String -> Maybe Expr
parseLet s = case (parse expr s) of
                [(n,[])] -> Just n
                [] -> Nothing

var :: Parser Expr
var = do  x <- symbol "x"
          v <- natural
          return (Var v)

app :: Parser Expr
app = do (x:e) <- appHelper
         return (foldl(\x y -> (App x y)) x e)

--storing all application variables in a list so that
--the list can then be iterated from left to right and thus enforce left association
appHelper :: Parser [Expr]
appHelper = do e <- some expr2
               return e

letP :: Parser Expr
letP = do l <- symbol "let"
          x <- symbol "x"
          n <- natural
          ns <- many (do symbol "x"; natural)
          eq <- symbol "="
          e1 <- expr
          i <- symbol "in"
          e2 <- expr
          return (Let (n:ns) e1 e2)

brack :: Parser Expr
brack = do o <- symbol "("
           e <- expr
           c <- symbol ")"
           return e

expr :: Parser Expr
expr = app <|> expr2
expr2 = brack <|>expr3
expr3 = letP <|> var

-- Challenge 4
-- count reductions using two different strategies
-- my solution for this challenge is based on Dr Rathke's interpreter from lecture 13
countReds :: LamExpr -> Int -> (Maybe Int, Maybe Int)
-- four possible cases
countReds e limit | numL <= limit && numR <= limit = (Just numL, Just numR)
                  | numL <= limit && numR > limit = (Just numL, Nothing)
                  | numL > limit && numR <= limit = (Nothing, Just numR)
                  | numL > limit && numR > limit = (Nothing, Nothing)
                  where
                    numL = length(traceL e)
                    numR = length(traceR e)

free :: Int -> LamExpr -> Bool
free x (LamVar y) =  x == y
free x (LamAbs y e) | x == y = False
free x (LamAbs y e) | x /= y = free x e
free x (LamApp e1 e2)  = (free x e1) || (free x e2)

rename x = -x

subst :: LamExpr -> Int ->  LamExpr -> LamExpr
subst (LamVar x) y e | x == y = e
subst (LamVar x) y e | x /= y = LamVar x
subst (LamAbs x e1) y e  |  x /= y && not (free x e)  = LamAbs x (subst e1 y e)
subst (LamAbs x e1) y e  |  x /= y &&     (free x e)  = let x' = rename x in subst (LamAbs x' (subst e1 x (LamVar x'))) y e
subst (LamAbs x e1) y e  | x == y  = LamAbs x e1
subst (LamApp e1 e2) y e = LamApp (subst e1 y e) (subst e2 y e)

evalLeft :: LamExpr -> LamExpr
evalLeft (LamVar x) = LamVar x
evalLeft (LamAbs x e) = (LamAbs x (evalLeft e))
evalLeft (LamApp e@(LamAbs x e1) e2) = subst e1 x e2
evalLeft (LamApp (LamVar x) e) = LamApp (LamVar x) (evalLeft e)
evalLeft (LamApp e1 e2) = LamApp (evalLeft e1) e2

evalRight :: LamExpr -> LamExpr
evalRight (LamVar x) = LamVar x
evalRight (LamAbs x e) = (LamAbs x (evalRight e))
evalRight (LamApp e@(LamAbs x e1) e2) = subst e1 x e2
evalRight (LamApp e (LamVar x)) = LamApp (evalRight e) (LamVar x)
evalRight (LamApp e1 e2) = LamApp e1 (evalRight e2)

reductions :: (LamExpr -> LamExpr) -> LamExpr -> [ (LamExpr, LamExpr) ]
reductions ss e = [ p | p <- zip evals (tail evals) ]
   where evals = iterate ss e

eval :: (LamExpr -> LamExpr) -> LamExpr -> LamExpr
eval ss = fst . head . dropWhile (uncurry (/=)) . reductions ss

trace :: (LamExpr -> LamExpr) -> LamExpr -> [LamExpr]
trace ss  = (map fst) . takeWhile (uncurry (/=)) .  reductions ss

evalL = eval evalLeft
traceL = trace evalLeft

evalR = eval evalRight
traceR = trace evalRight


-- Challenge 5
-- compile an arithmetic expression into a lambda calculus equivalent
compileArith :: String -> Maybe LamExpr

--constant for church's successor operation
succFunc = LamAbs 1 (LamAbs 2 (LamAbs 3 (LamApp (LamVar 2) (LamApp (LamApp (LamVar 1) (LamVar 2)) (LamVar 3)))))

-- if the second value from the tuple that is returned from "churchexpr" is greater than 0
-- this means that the successor function has been applied
-- otherwise
compileArith s = case (parse churchexpr s) of
                [(n,[])] | snd(n) > 0 -> Just (LamApp (church (fst n)) succFunc)
                         | otherwise -> Just (church(fst n))
                [] -> Nothing
                otherwise -> Nothing

--the type of the parser is a tuple so that
--the value of the second element from the tuple can be used as a flag
--of whether successor function has been applied or not
nums :: Parser (Int, Int)
nums = do n <- natural
          return (n,0)

bracks :: Parser (Int,Int)
bracks = do  _ <- symbol "("
             e <- churchexpr
             _ <- symbol ")"
             return (fst(e), snd(e))

add :: Parser (Int,Int)
add = do n1 <- churchexpr1
         _ <- symbol "+"
         n2 <- churchexpr
         return (fst(n1) + fst(n2), snd(n1) + snd(n2))

section :: Parser (Int,Int)
section = do _ <- symbol "("
             _ <- symbol "+"
             e <- churchexpr1
             _ <- symbol ")"
             return (fst(e), snd(e) + 1)

sectionValue :: Parser (Int, Int)
sectionValue = do _ <- symbol "("
                  _ <- symbol "+"
                  e1 <- churchexpr1
                  _ <- symbol ")"
                  e2 <- churchexpr1
                  return (fst(e1) + fst(e2), snd(e1) + snd(e2))

churchexpr = add <|> sectionValue <|> section <|> churchexpr1
churchexpr1 = bracks<|> churchexpr2
churchexpr2 = nums

--converting a number to a lambda expression following churchencoding
church :: Int -> LamExpr
church n = LamAbs 1 (LamAbs 2 (churchInner n))

churchInner :: Int -> LamExpr
churchInner 0 = LamVar 2
churchInner n = LamApp (LamVar 1) (churchInner (n - 1))



--ADDITIONAL TEST CASES

--Challenge 1

{-,
AdditionalTest 1: convertLet (Let [1] (App (Var 2)(Var 3)) (Let [2] (Var 1) (App (Var 2) (Var 3))))
AdditionalTest 2: convertLet (Let [1,2,3,4] (Var 3) (App (Var 1) (Var 4)))

--Challenge 2

AdditionalTest 1: prettyPrint (App (Let [1] (Var 2) (Var 3)) (App (Var 2) (Var 3)))
AdditionalTest 2: prettyPrint (Let [1,2,3] (App (App (Var 2) (Var 5)) (Var 4)) (Var 1))
AdditionalTest 3: prettyPrint (Let [1,2,3,4] (App (App (Var 2) (Var 5)) (Var 4)) (App (Var 6) (Var 1)))
AdditionalTest 4: prettyPrint (App (App (Var 4) (Var 1)) (App (Var 2) (Var 3)))

--Challenge 3

AdditionalTest 1: parseLet "x1 x2 x3 x4"
AdditionalTest 2: parseLet "let x1 x2 x3 = x2 in x1 x1 x3"

--Challenge 4

AdditionalTest 1: countReds (LamApp (LamAbs 1 (LamApp (LamVar 1) (LamVar 4))) (LamAbs 2 (LamAbs 3 (LamAbs 4 (LamVar 3))))) 4
AdditionalTest 2: countReds (LamApp (LamAbs 1 (LamApp (LamVar 1) (LamVar 4))) (LamAbs 2 (LamAbs 3 (LamAbs 4 (LamVar 3))))) 1
AdditionalTest 3: countReds (LamAbs 1 (LamAbs 2 (LamApp (LamVar 1) (LamApp (LamVar 1) (LamVar 2))))) 2

--Challenge 5

AdditionalTest 1: compileArith "(1) 1"
AdditionalTest 2: compileArith "(+1) (1+1)"
AdditionalTest 3: compileArith "(+1)1"
AdditionalTest 4: compileArith "(5)"
AdditionalTest 5: compileArith "(+1) + 1"
 -}
