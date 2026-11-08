-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn11_stopped_condexp_initial_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:22:30.645201+00:00
-- url     : https://prove2.me/submissions/dbb2b1f0-07dc-4034-8b45-67a261aa31c6

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Stopping-time conditional mean zero propagates to every initial event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hStoppedZero : ∀ᵐ ω ∂P,
      condExp hτstop.measurableSpace P M ω = 0)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    (∫ ω in A, M ω ∂P) = 0 := by
  have hm : hτstop.measurableSpace ≤ mΩ :=
    hτstop.measurableSpace_le
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hInitialSub :
      (𝓕.rightCont 0) ≤ hτstop.measurableSpace := by
    apply hτstop.le_measurableSpace_of_const_le
    intro ω
    change (↑(0 : ℝ≥0) : WithTop ℝ≥0) ≤
      (↑(τ ω) : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr (by positivity)
  have hInitialZero :
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0 := by
    calc
      condExp (𝓕.rightCont 0) P M =ᵐ[P]
        condExp (𝓕.rightCont 0) P
          (condExp hτstop.measurableSpace P M) :=
        (condExp_condExp_of_le hInitialSub hm).symm
      _ =ᵐ[P] condExp (𝓕.rightCont 0) P (fun _ => (0 : ℝ)) :=
        condExp_congr_ae hStoppedZero
      _ =ᵐ[P] (fun _ => (0 : ℝ)) := by simp
  have hm0 : 𝓕.rightCont 0 ≤ mΩ := (𝓕.rightCont).le 0
  haveI : SigmaFinite (P.trim hm0) := inferInstance
  have hCondInt := setIntegral_condExp hm0 hMI hA
  calc
    (∫ ω in A, M ω ∂P) =
        ∫ ω in A, condExp (𝓕.rightCont 0) P M ω ∂P :=
      hCondInt.symm
    _ = ∫ _ in A, (0 : ℝ) ∂P := by
      apply setIntegral_congr_ae (hm0 A hA)
      filter_upwards [hInitialZero] with ω hzero hω
      exact hzero
    _ = 0 := by simp
