-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin22_original_strict_pre_upper_clock_value_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:27:45.0752+00:00
-- url     : https://prove2.me/submissions/c73d09c7-9720-455a-8974-c3414f5fd7fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < twoSidedExitUpTime X b ω) :
    X.X t ω ≤ b := by
  by_contra h
  have hstrict : b < X.X t ω := lt_of_not_ge h
  have hle : twoSidedExitUpTime X b ω ≤ (t : ℝ≥0∞) := by
    simpa only [sub_zero] using
      (twoSidedExitUpTime_le_observation_of_strict_exceedance
        X b 0 ω t (by simpa only [sub_zero] using hstrict))
  exact (not_le.mpr ht) hle
