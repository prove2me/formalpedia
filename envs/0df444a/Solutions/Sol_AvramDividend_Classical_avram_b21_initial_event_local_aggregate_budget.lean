-- Prove2me | solution 1 for AvramDividend.Classical.avram_b21_initial_event_local_aggregate_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:57:10.547445+00:00
-- url     : https://prove2.me/submissions/60da8a9b-c447-4b8d-a8cc-0a2028339ecf

import Mathlib.Probability.Process.Filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- An initially measurable event needs only locally integrable aggregate noise, not global channel moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F M Err : Ω → ℝ)
    (hFI : IntegrableOn F A P)
    (hMI : IntegrableOn M A P)
    (hEI : IntegrableOn Err A P)
    (hMzero : (∫ ω in A, M ω ∂P) = 0)
    (hUpper : ∀ᵐ ω ∂(P.restrict A), F ω ≤ b + M ω + Err ω) :
    (∫ ω in A, F ω ∂P) ≤
      b * (P A).toReal + (∫ ω in A, Err ω ∂P) := by
  have hCI : IntegrableOn (fun _ : Ω => b) A P := integrable_const b
  have hRI : IntegrableOn (fun ω => b + M ω + Err ω) A P :=
    (hCI.add hMI).add hEI
  have hBound : (∫ ω in A, F ω ∂P) ≤
      (∫ ω in A, b + M ω + Err ω ∂P) :=
    integral_mono_ae hFI hRI hUpper
  have hFirst :
      (∫ ω in A, b + M ω + Err ω ∂P) =
      (∫ ω in A, b + M ω ∂P) +
      (∫ ω in A, Err ω ∂P) := by
    simpa only [Pi.add_apply] using (integral_add (hCI.add hMI) hEI)
  have hSecond :
      (∫ ω in A, b + M ω ∂P) =
      (∫ ω in A, (b : ℝ) ∂P) +
      (∫ ω in A, M ω ∂P) := by
    simpa only [Pi.add_apply] using (integral_add hCI hMI)
  rw [hFirst, hSecond] at hBound
  simpa [hMzero, integral_const, Measure.restrict_apply_univ,
    Measure.real, smul_eq_mul, mul_comm, add_assoc] using hBound
