-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn11_initial_event_zero_to_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:35:29.7383+00:00
-- url     : https://prove2.me/submissions/16cabc04-071e-4fa3-9575-6d1669214b26

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Initial-event orthogonality characterises conditional expectation zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hZero : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, M ω ∂P) = 0) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0 := by
  have hm : 𝓕.rightCont 0 ≤ mΩ := (𝓕.rightCont).le 0
  haveI : SigmaFinite (P.trim hm) := inferInstance
  have hz : (fun _ : Ω => (0 : ℝ)) =ᵐ[P]
      condExp (𝓕.rightCont 0) P M := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hMI
    · intro s hs hfinite
      exact (integrable_const (0 : ℝ)).integrableOn
    · intro s hs hfinite
      simpa using (hZero s hs).symm
    · fun_prop
  exact hz.symm
