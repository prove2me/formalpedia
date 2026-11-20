-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:57:52.234455+00:00
-- url     : https://prove2.me/submissions/d04e5937-1272-4786-9142-f521117fdc80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω ≠ 0} := by
  have hZero : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω = 0} := by
    convert hσ.measurableSet_le (0 : ℝ≥0) using 1
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe, nonpos_iff_eq_zero]
  simpa only [Set.compl_setOf] using hZero.compl
