-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:43:23.286575+00:00
-- url     : https://prove2.me/submissions/19ec6cfc-aeaf-4408-b9ba-099dd8a4c0ff

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (i r : ℝ≥0) (hir : i < r)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont i] A) :
    MeasurableSet[𝓕 r] A := by
  have hle : 𝓕.rightCont i ≤ 𝓕 r := by
    rw [𝓕.rightCont_eq i]
    exact iInf₂_le r hir
  exact hle A hA
