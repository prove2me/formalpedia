-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.shannon_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:02.62274+00:00
-- url     : https://prove2.me/submissions/0ec5db8f-0ade-4efb-b59f-a259e4e7b687

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
theorem _root_.solution [Nonempty ι] :
    shannon (fun _ : ι => 1 / (Fintype.card ι : ℝ)) = Real.log (Fintype.card ι) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [shannon, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    one_div, Real.log_inv, neg_mul, mul_neg, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
end BalanceSpecification.FiniteEntropy
