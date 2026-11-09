-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top11_original_zero_nu_global_continuous_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:26:59.92519+00:00
-- url     : https://prove2.me/submissions/f335acb1-988b-47b9-99d6-d0043005b2cf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_path_continuous_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! Original zero-jump paths are continuous at zero and every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X.X t ω) := by
  filter_upwards [avram_ubv_top11_original_zero_nu_path_continuous_ae
    X hNuZero] with ω hpos
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    simpa only [Set.Ici_zero_eq_univ, continuousWithinAt_univ] using X.rightCont ω 0
  · have hnonneg : (0 : ℝ≥0) ≤ t := bot_le
    exact hpos t (lt_of_le_of_ne hnonneg (Ne.symm ht))
