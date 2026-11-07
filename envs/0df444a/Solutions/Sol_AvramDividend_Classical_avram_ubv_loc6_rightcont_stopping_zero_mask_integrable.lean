-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:00:38.178764+00:00
-- url     : https://prove2.me/submissions/6aa7da7c-7042-4e01-b1e2-df14b3232fdd

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- A right-continuous-filtration stopping clock has a measurable zero event;
    masking an L1 payoff by a finite initial reward preserves L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ) :
    Integrable (fun ω => if σ ω = 0 then b else F ω) P := by
  classical
  have hσmeas : Measurable (fun ω => (σ ω : WithTop ℝ≥0)) :=
    hσstop.measurable.mono hσstop.measurableSpace_le le_rfl
  have hZero : MeasurableSet {ω : Ω | σ ω = 0} := by
    have hPre : MeasurableSet
        ((fun ω => (σ ω : WithTop ℝ≥0)) ⁻¹' {(0 : WithTop ℝ≥0)}) :=
      hσmeas (measurableSet_singleton (0 : WithTop ℝ≥0))
    have heq : {ω : Ω | σ ω = 0} =
        ((fun ω => (σ ω : WithTop ℝ≥0)) ⁻¹' {(0 : WithTop ℝ≥0)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact WithTop.coe_inj.symm
    rw [heq]
    exact hPre
  change Integrable
    (Set.piecewise {ω : Ω | σ ω = 0} (fun _ => b) F) P
  exact MeasureTheory.Integrable.piecewise hZero
    (integrable_const b).integrableOn hFI.integrableOn
