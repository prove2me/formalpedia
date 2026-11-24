-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.divergence_eq_neg_shannon_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:32.510972+00:00
-- url     : https://prove2.me/submissions/93b2e8d0-1cf3-4d32-8e63-f0838e925dfc

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_mul_log_div

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p q : ι → ℝ}
    (hq : ∀ i, 0 < q i) :
    divergence p q = -shannon p - ∑ i, p i * Real.log (q i) := by
  unfold divergence shannon
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [neg_mul, neg_neg] using mul_log_div (hq i)
end BalanceSpecification.FiniteEntropy
