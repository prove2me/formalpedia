-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb24_vanishing_eventwise_error_initial_condexp_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:22:12.628835+00:00
-- url     : https://prove2.me/submissions/b49d69c0-cc02-4f3a-972d-3b755983b57e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Vanishing deterministic eventwise errors yield the initial conditional expectation bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (F : Ω → ℝ) (b : ℝ) (ε : ℕ → ℝ)
    (hFI : Integrable F P)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hEvent : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      ∀ k, (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal + ε k) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by
  apply avram_ubv_finite14_initial_event_budget_to_condexp F b hFI
  intro A hA
  have hConst : Tendsto (fun _ : ℕ => b * (P A).toReal)
      atTop (𝓝 (b * (P A).toReal)) :=
    tendsto_const_nhds
  have hLimit : Tendsto
      (fun k : ℕ => b * (P A).toReal + ε k)
      atTop (𝓝 (b * (P A).toReal)) := by
    simpa using hConst.add hε
  exact ge_of_tendsto hLimit
    (Filter.Eventually.of_forall (hEvent A hA))
