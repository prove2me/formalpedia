-- Prove2me | solution 1 for FrontierMathLean.dedekindPsi_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:55:58.432085+00:00
-- url     : https://prove2.me/submissions/402ebea0-3bfd-466a-8950-f30cb48b5f58

import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Theorems.Thm_FrontierMathLean_dedekindPsi_zero
import Theorems.Thm_FrontierMathLean_dedekindPsi_one
attribute [local simp] FrontierMathLean.dedekindPsi_zero
attribute [local simp] FrontierMathLean.dedekindPsi_one

set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  simp [dedekindPsi, hp.ne_zero, hp.primeFactors, hp.factorization]
end FrontierMathLean
