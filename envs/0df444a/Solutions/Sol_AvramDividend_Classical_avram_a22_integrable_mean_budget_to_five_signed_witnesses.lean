-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_integrable_mean_budget_to_five_signed_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:06:02.293426+00:00
-- url     : https://prove2.me/submissions/607bdec9-24d2-4d51-8846-9ca95ba6914c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hBudget : (∫ ω, F ω ∂P) ≤ b) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        F ω ≤ b + Mc ω + Ms ω + Ml ω + G ω + R ω)  := by
  let m : ℝ := ∫ ω, F ω ∂P
  let M : Ω → ℝ := fun ω => F ω - m
  let Z : Ω → ℝ := fun _ => 0
  let G : Ω → ℝ := fun _ => m - b
  have hMI : Integrable M P := hFI.sub (integrable_const m)
  have hM0 : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, F ω - m ∂P) = 0
    rw [integral_sub hFI (integrable_const m)]
    simp [m]
  refine ⟨M, Z, Z, G, Z, hMI, integrable_const 0,
    integrable_const 0, hM0, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Z]
  · simp [Z]
  · exact Filter.Eventually.of_forall (fun ω => by
      dsimp [G, m]
      linarith)
  · simp [Z]
  · exact Filter.Eventually.of_forall (fun ω => by
      dsimp [M, Z, G]
      linarith)
