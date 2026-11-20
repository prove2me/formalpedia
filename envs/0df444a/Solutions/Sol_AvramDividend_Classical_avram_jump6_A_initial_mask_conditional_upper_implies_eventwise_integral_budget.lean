-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:26:12.431415+00:00
-- url     : https://prove2.me/submissions/8e8a62f8-b13b-491b-a28a-665954b07ec3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (E : Set Ω) (hE : MeasurableSet[m] E)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (b : ℝ)
    (hCE : ∀ᵐ ω ∂P, condExp m P F ω ≤ b) :
    (∫ ω in E, F ω ∂P) ≤ b * (P E).toReal := by
  have hEbase : MeasurableSet[mΩ] E := hm E hE
  have hCEset : ∀ᵐ ω ∂(P.restrict E), condExp m P F ω ≤ b :=
    ae_restrict_of_ae hCE
  have hCI : IntegrableOn (condExp m P F) E P :=
    (integrable_condExp).integrableOn
  have hBI : IntegrableOn (fun _ : Ω => b) E P := integrable_const b
  have hUpper :
      (∫ ω in E, condExp m P F ω ∂P) ≤
        (∫ _ω in E, b ∂P) :=
    integral_mono_ae hCI hBI hCEset
  have hEq :
      (∫ ω in E, condExp m P F ω ∂P) =
        (∫ ω in E, F ω ∂P) :=
    setIntegral_condExp hm hFI hE
  rw [hEq] at hUpper
  simpa [integral_const, Measure.real, smul_eq_mul, mul_comm] using hUpper
