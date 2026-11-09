-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_condexp_upper_to_centred_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T08:18:58.112204+00:00
-- url     : https://prove2.me/submissions/57ef5bd8-a946-489e-b36b-a9468c73b4f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_initial_event_zero_to_condexp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F : Ω → ℝ) (hFI : Integrable F P)
    (hCondUpper : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b) :
    ∃ M : Ω → ℝ, Integrable M P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ b + M ω) := by
  let M : Ω → ℝ := fun ω => F ω - condExp (𝓕.rightCont 0) P F ω
  have hMI : Integrable M P :=
    hFI.sub (integrable_condExp : Integrable (condExp (𝓕.rightCont 0) P F) P)
  have hm : (𝓕.rightCont 0) ≤ mΩ := (𝓕.rightCont).le 0
  have hZero : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, M ω ∂P) = 0 := by
    intro A hA
    have hFIA : IntegrableOn F A P := hFI.integrableOn
    have hCA : IntegrableOn (condExp (𝓕.rightCont 0) P F) A P :=
      (integrable_condExp : Integrable (condExp (𝓕.rightCont 0) P F) P).integrableOn
    change (∫ ω in A, F ω - condExp (𝓕.rightCont 0) P F ω ∂P) = 0
    rw [integral_sub hFIA hCA, setIntegral_condExp hm hFI hA]
    exact sub_self _
  have hMzero :=
    avram_ubv_finite9_turn11_initial_event_zero_to_condexp_zero M hMI hZero
  refine ⟨M, hMI, hMzero, ?_⟩
  filter_upwards [hCondUpper] with ω hω
  dsimp [M]
  linarith
