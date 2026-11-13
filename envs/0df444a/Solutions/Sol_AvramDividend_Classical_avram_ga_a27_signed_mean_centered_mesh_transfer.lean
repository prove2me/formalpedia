-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_signed_mean_centered_mesh_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:31:07.497709+00:00
-- url     : https://prove2.me/submissions/74f056ac-fb7b-4519-8d41-62ed2ff13f37

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S M G : ℕ → Ω → ℝ)
    (hM : ∀ m : ℕ, Integrable (M m) P ∧
      (∫ ω, M m ω ∂P) = 0)
    (hSG : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => S m ω - G m ω) P ∧
      |∫ ω, S m ω - G m ω ∂P| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => S m ω - M m ω - G m ω) P ∧
      |∫ ω, S m ω - M m ω - G m ω ∂P| ≤ ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := hSG ε hε
  refine ⟨k, ?_⟩
  intro m hm
  obtain ⟨hAI, hAε⟩ := hk m hm
  obtain ⟨hMI, hM0⟩ := hM m
  have hEq : (fun ω => S m ω - M m ω - G m ω) =
      (fun ω => (S m ω - G m ω) - M m ω) := by
    funext ω
    ring
  rw [hEq]
  refine ⟨hAI.sub hMI, ?_⟩
  rw [integral_sub hAI hMI, hM0, sub_zero]
  exact hAε
