-- Prove2me | solution 2 for BalanceSpecification.FiniteEntropy.mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:47.495297+00:00
-- url     : https://prove2.me/submissions/aed41d30-e1eb-47cc-b5f4-f103d230f960

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p q : ℝ} (hq : 0 < q) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  by_cases hz : p = 0
  · simp only [hz, zero_mul, sub_zero]
  · rw [Real.log_div hz hq.ne', mul_sub]
end BalanceSpecification.FiniteEntropy
