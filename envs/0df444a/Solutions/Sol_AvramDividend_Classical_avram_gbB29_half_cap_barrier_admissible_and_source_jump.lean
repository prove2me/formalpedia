-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB29_half_cap_barrier_admissible_and_source_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:03:31.60235+00:00
-- url     : https://prove2.me/submissions/77ba6bd5-5d20-4a57-9255-02e6526e7fc1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) :
    IsAdmissibleLe X (1 / 2 : ℝ) (ENNReal.ofReal (1 / 2 : ℝ))
      (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) <
        ruinTime X (1 / 2 : ℝ) (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) ω) →
      rightLimit (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω -
        barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ) t ω ≤
      w (riskProcess X (1 / 2 : ℝ) (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω) -
      w (riskProcess X (1 / 2 : ℝ) (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω -
        (rightLimit (barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ)) t ω -
         barrierStrategy X (1 / 2 : ℝ) (1 / 2 : ℝ) t ω)) := by 
  constructor
  · exact barrierStrategy_admissibleLe_nonnegative_barrier
      X (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  · intro ω t _
    have hr := barrierStrategy_no_right_jump_of_initial_below_barrier
      X (1 / 2 : ℝ) (1 / 2 : ℝ) (le_refl _) ω t
    simp only [hr, sub_self, sub_zero, le_refl]
