-- Prove2me | solution 1 for AvramDividend.Classical.avram_growth_20261123_original_corrected_exit_clocks_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:26:27.485175+00:00
-- url     : https://prove2.me/submissions/d809a7e1-5f0b-4712-8c16-7da7fb403127

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_corrected_killed_discount_measurable
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (b : ℝ) :
    Measurable (twoSidedExitUpTimeCorrected X (b - 1)) ∧
    Measurable (twoSidedExitDownTimeCorrected X (-1)) := by
  obtain ⟨hup, hdown, _⟩ :=
    AvramDividend.Classical.avram_p4_f6_hjb_corrected_killed_discount_measurable X (0 : ℝ) (-1) (b - 1)
  exact ⟨hup, hdown⟩
