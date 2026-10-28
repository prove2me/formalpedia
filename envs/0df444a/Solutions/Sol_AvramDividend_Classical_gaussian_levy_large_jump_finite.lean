-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_large_jump_finite
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:18:21.031751+00:00
-- url     : https://prove2.me/submissions/12ad9cec-e19f-41b5-b1a1-93697a049ea3

import Mathlib
open MeasureTheory Set

theorem solution (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    μ (Ici (1 : ℝ)) < ⊤ := by
  have hsub : Ici (1 : ℝ) ⊆ Ioi 0 := fun z hz => show (0:ℝ) < z from lt_of_lt_of_le one_pos (mem_Ici.1 hz)
  have h1 : μ (Ici (1 : ℝ)) = ∫⁻ z in Ici (1 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ := by
    rw [setLIntegral_congr_fun measurableSet_Ici (g := fun _ => (1 : ENNReal))]
    · simp
    · intro z hz
      have : (1 : ℝ) ≤ z ^ 2 := by nlinarith [mem_Ici.1 hz]
      simp [min_eq_left this]
  rw [h1]
  exact lt_of_le_of_lt (lintegral_mono_set hsub) hlevy
