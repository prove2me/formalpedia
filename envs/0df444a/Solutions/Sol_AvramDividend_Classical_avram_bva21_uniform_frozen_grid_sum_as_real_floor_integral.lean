-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:59:20.23732+00:00
-- url     : https://prove2.me/submissions/dda1d44c-1fcd-4ec8-8409-df01206f67c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_frozen_grid_sum_as_step_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- The full inclusive frozen Riemann sum is its exact real-time floor-step integral. -/
theorem solution
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (T / ((n : ℝ) + 2)) * c i) =
    ∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by
  let u : ℕ → ℝ := fun i => T * (i : ℝ) / ((n : ℝ) + 2)
  have hwidth (i : ℕ) :
      u (i + 1) - u i = T / ((n : ℝ) + 2) := by
    dsimp [u]
    push_cast
    ring
  have hmono : ∀ i < n + 1, u i ≤ u (i + 1) := by
    intro i hi
    have hδ : 0 ≤ T / ((n : ℝ) + 2) :=
      (div_pos hT (by positivity)).le
    linarith [hwidth i]
  calc
    (∑ i ∈ Finset.range (n + 1),
        (T / ((n : ℝ) + 2)) * c i) =
      ∑ i ∈ Finset.range (n + 1),
        (u (i + 1) - u i) * c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hwidth]
    _ = ∫ t : ℝ, ∑ i ∈ Finset.range (n + 1),
        (Ico (u i) (u (i + 1))).indicator
          (fun _ => c i) t :=
      (avram_bvb_b21_original_frozen_grid_sum_as_step_integral
        (n + 1) u c hmono).symm
    _ = ∫ t : ℝ,
        if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
        then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by
      apply integral_congr_ae
      filter_upwards [] with t
      simpa only [u] using
        (avram_bva20_uniform_step_full_floor_mask_identity T hT n c t)
