-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_original_corrected_finite_two_sided_exit_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:47:59.631216+00:00
-- url     : https://prove2.me/submissions/4409235b-0d6e-4de3-92bb-3dd4e313feb5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_growth_20261123_original_corrected_exit_clocks_measurable
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (n : ℕ) :
    Measurable (fun ω : Ω =>
      min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))) := by
  obtain ⟨hUp, hDown⟩ :=
    AvramDividend.Classical.avram_growth_20261123_original_corrected_exit_clocks_measurable X b
  exact hUp.min (hDown.min measurable_const)
