-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB46_original_barrier_dividend_jump_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:01:14.723194+00:00
-- url     : https://prove2.me/submissions/8b9502a6-f345-4da9-9311-8af2a6a6b5e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Continuous original cap-barrier dividends satisfy the exact jump budget. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) (w : ℝ → ℝ) :
  ∀ ω (t : ℝ≥0),
    rightLimit (barrierStrategy X c c) t ω -
      barrierStrategy X c c t ω ≤
    w (riskProcess X c (barrierStrategy X c c) t ω) -
      w (riskProcess X c (barrierStrategy X c c) t ω -
        (rightLimit (barrierStrategy X c c) t ω -
          barrierStrategy X c c t ω)) := by
  intro ω t
  have h :=
    avram_gbB41_original_barrier_postpayment_rightLimit_eq X c ω t
  simp [h]
