-- Prove2me | solution 1 for DerivativeChainPrivate.exists_chain_cost_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:50:19.671998+00:00
-- url     : https://prove2.me/submissions/5d4ac9db-3789-404c-8428-5acf2c94b453

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_sq_le
import Theorems.Thm_DerivativeChainPrivate_row_natDegree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

/-!
# Exact derivative-row definitions and structural adapters

The four definitions below reproduce the definitions in the private mission
statement. No statement draft is imported. Rows are the actual, unnormalized
iterated derivatives: only the original row is asserted to be monic.
-/

open scoped BigOperators

namespace DerivativeChainPrivate





















/-- Positive-numbered rows in range are nonconstant. -/
theorem row_degree_pos {n m : ℕ} (a : Fin n → ℂ) (hm0 : 0 < m) (hmn : m ≤ n) :
    0 < (row a m).degree := by
  rw [← Polynomial.natDegree_pos_iff_degree_pos, row_natDegree a hmn]
  exact hm0









end DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ Real.sqrt ((n - 1 : ℕ) : ℝ) := by
  obtain ⟨u, hu⟩ := Complex.exists_root (row_degree_pos a (by omega) (by omega) :
    0 < (row a 1).degree)
  obtain ⟨z, hz, _, hcost⟩ := exists_chain_cost_sq_le hn a ha u hu
  refine ⟨z, hz, Real.le_sqrt_of_sq_le (hcost.trans ?_)⟩
  have : 1 - ‖u‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖u‖]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) by positivity)
