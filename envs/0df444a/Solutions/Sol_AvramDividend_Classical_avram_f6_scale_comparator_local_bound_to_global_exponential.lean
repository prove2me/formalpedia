-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_scale_comparator_local_bound_to_global_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:59:04.216413+00:00
-- url     : https://prove2.me/submissions/c536bf99-58a0-4000-9005-47fa487359a2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
set_option autoImplicit false
open MeasureTheory Set Topology
noncomputable section

theorem solution
    (w W : ℝ → ℝ) (θ A K0 K1 : ℝ)
    (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (hwLocal : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ K0)
    (hScale : ∀ y : ℝ, W y ≤ K1 * Real.exp (θ * y))
    (hComp : ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by
  let K : ℝ := max K0 (A * K1)
  have hK : 0 ≤ K := le_trans hK0 (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro y hy
  have he : 1 ≤ Real.exp (θ * y) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonneg hθ hy
  by_cases hsmall : y ≤ 1
  · calc
      w y ≤ K0 := hwLocal y hy hsmall
      _ ≤ K := le_max_left _ _
      _ ≤ K * Real.exp (θ * y) := by nlinarith
  · have hhigh : 1 ≤ y := le_of_lt (lt_of_not_ge hsmall)
    calc
      w y ≤ A * W y := hComp y hhigh
      _ ≤ A * (K1 * Real.exp (θ * y)) :=
        mul_le_mul_of_nonneg_left (hScale y) hA
      _ ≤ K * Real.exp (θ * y) := by
        have hm : A * K1 ≤ K := le_max_right _ _
        nlinarith [Real.exp_pos (θ * y)]
