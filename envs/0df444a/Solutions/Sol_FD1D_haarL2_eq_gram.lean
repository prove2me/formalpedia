-- Prove2me | solution 1 for FD1D.haarL2_eq_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:10.301847+00:00
-- url     : https://prove2.me/submissions/9251ae94-c410-470f-86e6-397eddd93107

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_mul_integrable
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    haarL2 l p b =
      ∑ i, ∑ j, (b i * b j) *
        ∫ z, dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z := by
  unfold haarL2 haarCombination
  rw [show (fun z : ℝ => (∑ i, b i * dyadicTent (l i) (p i) z) ^ 2) =
      fun z => ∑ i, ∑ j, (b i * b j) *
        (dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z) by
    funext z
    simp only [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [MeasureTheory.integral_const_mul]
    · intro j _
      exact (dyadicTent_mul_integrable _ _ _ _ (hp i)).const_mul _
  · intro i _
    exact MeasureTheory.integrable_finsetSum _ fun j _ =>
      (dyadicTent_mul_integrable _ _ _ _ (hp i)).const_mul _
end FD1D
