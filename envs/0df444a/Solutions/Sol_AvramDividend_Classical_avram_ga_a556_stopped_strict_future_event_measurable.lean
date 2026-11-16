-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a556_stopped_strict_future_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:31:19.981566+00:00
-- url     : https://prove2.me/submissions/9079b43c-d111-4c43-88c5-6f36593fc3d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) (s : ℝ≥0) :
    MeasurableSet {ω : Ω | s < ρ ω} := by
  have hs : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < ρ ω} := by
    have he : {ω : Ω | s < ρ ω} =
        {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ s}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
        WithTop.coe_le_coe, not_le]
    rw [he]
    exact (hρstop s).compl
  exact (𝓕.rightCont.le s) _ hs
