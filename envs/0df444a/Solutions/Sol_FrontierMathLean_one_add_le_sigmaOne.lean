-- Prove2me | solution 1 for FrontierMathLean.one_add_le_sigmaOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:55:56.609807+00:00
-- url     : https://prove2.me/submissions/d66d282b-d343-44da-8154-11a2ceada08b

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
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    n + 1 ≤ ArithmeticFunction.sigma 1 n := by
  have hn0 : n ≠ 0 := by omega
  rw [ArithmeticFunction.sigma_one_apply]
  calc
    n + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d := by
      rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        omega
      · simp only [mem_singleton]
        omega
    _ ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro d hd
        simp only [mem_insert, mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Nat.one_mem_divisors.mpr hn0
        · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩) (by
          intro d _ _
          exact Nat.zero_le d)
end FrontierMathLean
