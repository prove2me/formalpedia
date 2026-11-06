-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_signed_residual_to_three_original_source_slots
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:36:31.375198+00:00
-- url     : https://prove2.me/submissions/0ab69957-fccb-4a3e-98ad-86e1419514c9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- A single signed stopped residual splits into the canonical three noise slots. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (a : ℝ) (Term Cash : Ω → ℝ)
    (h : ∃ M U V : Ω → ℝ,
      Integrable M P ∧ Integrable U P ∧ Integrable V P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, U ω + V ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ a + M ω + U ω + V ω)) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        a + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  rcases h with ⟨M, U, V, hMI, hUI, hVI, hM0, hNonpos, hBudget⟩
  have hZero : Integrable (fun _ : Ω => (0 : ℝ)) P := integrable_zero Ω ℝ P
  refine ⟨M, (fun _ => 0), (fun _ => 0), (fun ω => U ω + V ω),
    (fun _ => 0), hMI, hZero, hZero, hUI.add hVI, hM0,
    ?_, ?_, hNonpos, ?_, ?_⟩
  · simp
  · simp
  · filter_upwards [] with ω
    exact le_refl 0
  · filter_upwards [hBudget] with ω hω
    simpa only [add_zero, zero_add, add_assoc] using hω
