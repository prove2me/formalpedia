-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_zero_barrier_HJB_right_payment_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:51:09.39531+00:00
-- url     : https://prove2.me/submissions/429a22ff-f02b-4aa6-ac02-c51bf31231f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω) →
      rightLimit (barrierStrategy X 0 0) t ω -
        barrierStrategy X 0 0 t ω ≤
        w (riskProcess X 0 (barrierStrategy X 0 0) t ω) -
          w (riskProcess X 0 (barrierStrategy X 0 0) t ω -
            (rightLimit (barrierStrategy X 0 0) t ω -
              barrierStrategy X 0 0 t ω)) := by
  intro ω t _
  rw [barrierStrategy_no_right_jump_of_initial_below_barrier
    X 0 0 (le_refl 0) ω t]
  simp
