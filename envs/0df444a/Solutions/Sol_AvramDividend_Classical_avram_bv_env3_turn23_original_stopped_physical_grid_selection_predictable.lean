-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:55:54.646665+00:00
-- url     : https://prove2.me/submissions/cafdb744-bb36-413e-b8d9-ceda392b6379

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Before a genuine original stopping time, the physical-grid source event is known at its left endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (i : ℕ) :
    MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} := by
  have hBefore :
      {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} =
        {ω : Ω | τ ω ≤ (u i : WithTop ℝ≥0)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [hBefore]
  exact (hStop (u i)).compl
