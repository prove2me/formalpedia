-- Prove2me | solution 1 for FrontierMathLean.totient_le_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:46:53.102569+00:00
-- url     : https://prove2.me/submissions/1004d528-9596-477a-ac5d-d949f3a5a3c1

import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Definitions.Def_FrontierMathLean_DimitrovConjecture1

set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) : n.totient ≤ n - 1 :=
  Nat.le_sub_one_of_lt (Nat.totient_lt n (by omega))
end FrontierMathLean
