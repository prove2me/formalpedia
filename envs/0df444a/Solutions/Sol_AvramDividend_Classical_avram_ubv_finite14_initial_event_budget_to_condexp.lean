-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite14_initial_event_budget_to_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:55:07.688963+00:00
-- url     : https://prove2.me/submissions/fe62326b-31d4-4a03-9998-b2b9017f2888

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Event budgets on the initial sigma algebra determine the conditional bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (F : Ω → ℝ) (b : ℝ) (hFI : Integrable F P)
    (hBudget : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by
  classical
  let m : MeasurableSpace Ω := 𝓕.rightCont 0
  have hm : m ≤ mΩ := (𝓕.rightCont).le 0
  let μ := P.trim hm
  letI : IsFiniteMeasure μ := MeasureTheory.isFiniteMeasure_trim hm
  have hSM : StronglyMeasurable[m] (condExp m P F) :=
    stronglyMeasurable_condExp
  have hInt : Integrable (condExp m P F) μ :=
    (integrable_condExp : Integrable (condExp m P F) P).trim hm hSM
  have hEqCond (A : Set Ω) (hA : MeasurableSet[m] A) :
      (∫ ω in A, condExp m P F ω ∂P) =
        ∫ ω in A, condExp m P F ω ∂μ := by
    calc
      (∫ ω in A, condExp m P F ω ∂P) =
          ∫ ω, A.indicator (condExp m P F) ω ∂P :=
        (integral_indicator (hm A hA)).symm
      _ = ∫ ω, A.indicator (condExp m P F) ω ∂μ :=
        integral_trim hm (hSM.indicator hA)
      _ = ∫ ω in A, condExp m P F ω ∂μ := integral_indicator hA
  have hEqConst (A : Set Ω) (hA : MeasurableSet[m] A) :
      (∫ ω in A, (b : ℝ) ∂P) =
        ∫ ω in A, (b : ℝ) ∂μ := by
    calc
      (∫ ω in A, (b : ℝ) ∂P) =
          ∫ ω, A.indicator (fun _ : Ω => b) ω ∂P :=
        (integral_indicator (hm A hA)).symm
      _ = ∫ ω, A.indicator (fun _ : Ω => b) ω ∂μ :=
        integral_trim hm (stronglyMeasurable_const.indicator hA)
      _ = ∫ ω in A, (b : ℝ) ∂μ := integral_indicator hA
  have hLeBase (A : Set Ω) (hA : MeasurableSet[m] A) :
      (∫ ω in A, condExp m P F ω ∂P) ≤
        ∫ ω in A, (b : ℝ) ∂P := by
    rw [setIntegral_condExp hm hFI hA]
    simpa [integral_const, Measure.real_def, smul_eq_mul, mul_comm] using hBudget A hA
  have hLeTrim : (condExp m P F) ≤ᵐ[μ] (fun _ : Ω => b) := by
    apply ae_le_of_forall_setIntegral_le hInt (integrable_const _)
    intro A hA hFinite
    rw [← hEqCond A hA, ← hEqConst A hA]
    exact hLeBase A hA
  exact ae_le_of_ae_le_trim hLeTrim
