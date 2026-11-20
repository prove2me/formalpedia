-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_eventwise_integrable_budget_to_signed_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:45:49.260843+00:00
-- url     : https://prove2.me/submissions/e8afed75-f234-4e58-96ca-8e954a677dfe

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (b : ℝ) (F M : Ω → ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hMzero : (∫ ω in A, M ω ∂P) = 0)
    (hBudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ Err : ℕ → Ω → ℝ,
      (∀ m, IntegrableOn (Err m) A P) ∧
      (∀ m, ∀ᵐ ω ∂(P.restrict A),
        F ω ≤ b + M ω + Err m ω) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ m, (∫ ω in A, Err m ω ∂P) ≤ ε) := by
  let E : Ω → ℝ := fun ω => F ω - b - M ω
  have hEI : Integrable E P :=
    (hFI.sub (integrable_const b)).sub hMI
  have hInt :
      (∫ ω in A, E ω ∂P) =
        (∫ ω in A, F ω ∂P) - b * (P A).toReal := by
    dsimp [E]
    rw [integral_sub, integral_sub]
    · simp only [hMzero, sub_zero]
      simp only [integral_const]
      simp [Measure.real, Measure.restrict_apply]
      ring
    · exact hFI.integrableOn
    · exact (integrable_const b).integrableOn
    · exact (hFI.sub (integrable_const b)).integrableOn
    · exact hMI.integrableOn
  have hENonpos : (∫ ω in A, E ω ∂P) ≤ 0 := by
    rw [hInt]
    linarith
  refine ⟨fun _ => E, (fun m => hEI.integrableOn), ?_, ?_⟩
  · intro m
    filter_upwards [] with ω
    dsimp [E]
    linarith
  · intro ε hε
    refine ⟨0, ?_⟩
    exact hENonpos.trans (le_of_lt hε)