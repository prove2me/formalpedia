-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_positive_clock_initial_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T08:07:04.293632+00:00
-- url     : https://prove2.me/submissions/b67569b7-48e6-48bd-b0bf-6393cccb88ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω ≠ 0} := by
  have hz : MeasurableSet[𝓕.rightCont 0]
      {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ (0 : WithTop ℝ≥0)} :=
    hσstop 0
  have hset : {ω : Ω | σ ω = 0} =
      {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ (0 : WithTop ℝ≥0)} := by
    ext ω
    constructor
    · intro h
      change (↑(σ ω) : WithTop ℝ≥0) ≤
        (↑(0 : ℝ≥0) : WithTop ℝ≥0)
      exact WithTop.coe_le_coe.mpr (le_of_eq h)
    · intro h
      have hh : σ ω ≤ (0 : ℝ≥0) := by
        change (↑(σ ω) : WithTop ℝ≥0) ≤
          (↑(0 : ℝ≥0) : WithTop ℝ≥0) at h
        exact WithTop.coe_le_coe.mp h
      exact le_antisymm hh (by positivity)
  have hzero : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω = 0} := by
    rw [hset]
    exact hz
  simpa only [Set.compl_setOf] using hzero.compl
