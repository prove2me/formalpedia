-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:27:31.488318+00:00
-- url     : https://prove2.me/submissions/f92d65ad-04c1-4fb7-9229-753883564c58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_path_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonjump_iff_continuous_at

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! A single original full-measure event makes every positive-time actual
source jump mark vanish, suitable for removing source jump corrections. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = 0 := by
  filter_upwards [avram_ubv_top11_original_zero_nu_path_continuous_ae
    X hNuZero] with ω hcontinuous
  intro t ht
  exact (avram_wave4_04a_actual_source_nonjump_iff_continuous_at
    X ω t ht).mpr (hcontinuous t ht)
