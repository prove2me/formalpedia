-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_singular_density_restrict_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:41:25.133801+00:00
-- url     : https://prove2.me/submissions/3e773a91-0dab-46a3-b418-e326ff410ee1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_bochner_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The singular Levy-density expectation is a restricted Bochner integral. -/
theorem solution (g : ℝ → ℝ) :
    (∫ z, g z ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) =
    (∫ z in Ioo (-1 : ℝ) 0,
      |z| ^ (-(3 / 2 : ℝ)) * g z ∂volume) := by
  rw [avram_gen14_singular_density_bochner_integral]
  calc
    (∫ z, (if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0).toReal * g z ∂volume) =
      ∫ z, (Ioo (-1 : ℝ) 0).indicator
        (fun z => |z| ^ (-(3 / 2 : ℝ)) * g z) z ∂volume := by
        congr 1
        funext z
        by_cases hz : z ∈ Ioo (-1 : ℝ) 0
        · simp [hz, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg z) _)]
        · simp [hz]
    _ = (∫ z in Ioo (-1 : ℝ) 0,
          |z| ^ (-(3 / 2 : ℝ)) * g z ∂volume) := by
        rw [integral_indicator measurableSet_Ioo]
