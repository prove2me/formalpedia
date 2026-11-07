-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_scale_dominated_growth_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:13:11.71729+00:00
-- url     : https://prove2.me/submissions/70a92dfb-5777-492d-b12d-9b7886e02535

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

noncomputable section

theorem solution
    (w W : ℝ → ℝ) (θ A K M : ℝ)
    (hθ : 0 ≤ θ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hneg : ∀ y < 0, w y = 0)
    (hunit : ∀ y, 0 ≤ y → y ≤ 1 → w y ≤ M)
    (hdom : ∀ y, 1 ≤ y → w y ≤ A * W y)
    (hW : ∀ y, W y ≤ K * Real.exp (θ * y)) :
    ∀ y : ℝ, w y ≤ max M (A * K) * Real.exp (θ * y) := by
  intro y
  have hmax : 0 ≤ max M (A * K) := hM.trans (le_max_left _ _)
  by_cases hyneg : y < 0
  · rw [hneg y hyneg]
    exact mul_nonneg hmax (le_of_lt (Real.exp_pos _))
  by_cases hyone : y ≤ 1
  · have hy0 : 0 ≤ y := le_of_not_gt hyneg
    have hθy : 0 ≤ θ * y := mul_nonneg hθ hy0
    have he : 1 ≤ Real.exp (θ * y) := by
      have := Real.add_one_le_exp (θ * y)
      linarith
    have hmul : max M (A * K) ≤ max M (A * K) * Real.exp (θ * y) := by
      nlinarith [mul_nonneg hmax (sub_nonneg.mpr he)]
    exact (hunit y hy0 hyone).trans ((le_max_left _ _).trans hmul)
  · have hy1 : 1 ≤ y := by linarith
    calc
      w y ≤ A * W y := hdom y hy1
      _ ≤ A * (K * Real.exp (θ * y)) :=
        mul_le_mul_of_nonneg_left (hW y) hA
      _ = (A * K) * Real.exp (θ * y) := by ring
      _ ≤ max M (A * K) * Real.exp (θ * y) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (Real.exp_pos _))
