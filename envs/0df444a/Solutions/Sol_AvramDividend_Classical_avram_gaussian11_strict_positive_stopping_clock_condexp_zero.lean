-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian11_strict_positive_stopping_clock_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:32:21.228371+00:00
-- url     : https://prove2.me/submissions/5f9f8f7c-1d08-4d44-a1c7-9ad0b8e19ac3

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, M ω ∂P) = 0 := by
  have hm : (𝓕.rightCont 0) ≤ mΩ := (𝓕.rightCont).le 0
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hZero :
      MeasurableSet[𝓕.rightCont 0]
        {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ (0 : WithTop ℝ≥0)} :=
    hσstop 0
  have hEq :
      {ω : Ω | σ ω = 0} =
        {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ (0 : WithTop ℝ≥0)} := by
    ext ω
    constructor
    · intro h
      change σ ω = 0 at h
      change (↑(σ ω) : WithTop ℝ≥0) ≤
        (↑(0 : ℝ≥0) : WithTop ℝ≥0)
      exact WithTop.coe_le_coe.mpr (le_of_eq h)
    · intro h
      have hh : σ ω ≤ (0 : ℝ≥0) := by
        change (↑(σ ω) : WithTop ℝ≥0) ≤
          (↑(0 : ℝ≥0) : WithTop ℝ≥0) at h
        exact WithTop.coe_le_coe.mp h
      exact le_antisymm hh (by positivity)
  have hZeroEvent :
      MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω = 0} := by
    rw [hEq]
    exact hZero
  have hEvent :
      MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω ≠ 0} := by
    simpa only [Set.compl_setOf] using hZeroEvent.compl
  have hCondRestrict :
      ∀ᵐ ω ∂P.restrict {ω : Ω | σ ω ≠ 0},
        condExp (𝓕.rightCont 0) P M ω = 0 :=
    ae_restrict_of_ae hCondZero
  have hSetIntegral := setIntegral_condExp hm hMI hEvent
  calc
    (∫ ω in {ω : Ω | σ ω ≠ 0}, M ω ∂P) =
      (∫ ω in {ω : Ω | σ ω ≠ 0},
        condExp (𝓕.rightCont 0) P M ω ∂P) := hSetIntegral.symm
    _ = 0 := by
      rw [integral_congr_ae hCondRestrict]
      simp
