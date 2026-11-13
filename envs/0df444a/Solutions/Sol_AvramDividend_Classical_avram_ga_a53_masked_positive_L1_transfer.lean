-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a53_masked_positive_L1_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:55:58.634172+00:00
-- url     : https://prove2.me/submissions/7241d012-eeba-4d28-bac2-1c4f5b92cf65

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : Ω → ℝ≥0) (f : ℕ → Ω → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (f m ω) (0 : ℝ) else 0) P ∧
      (∫ ω, (if 0 < ρ ω then max (f m ω) (0 : ℝ) else 0) ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (if 0 < ρ ω then f m ω else 0) (0 : ℝ)) P ∧
      (∫ ω, max (if 0 < ρ ω then f m ω else 0) (0 : ℝ) ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := h ε hε
  refine ⟨k, ?_⟩
  intro m hm
  have hEq :
      (fun ω => max (if 0 < ρ ω then f m ω else 0) (0 : ℝ)) =
      (fun ω => if 0 < ρ ω then max (f m ω) (0 : ℝ) else 0) := by
    funext ω
    by_cases hp : 0 < ρ ω <;> simp [hp]
  simpa only [hEq] using hk m hm
