-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_positive_l1_two_term_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:42:28.235773+00:00
-- url     : https://prove2.me/submissions/2ca81243-db94-4800-bb1f-9976486da924

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Two one-sided L1 bounds give a one-sided L1 bound for their sum. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F A B : ℕ → Ω → ℝ)
    (hAB : ∀ m ω, F m ω = A m ω + B m ω)
    (hI : ∀ m, Integrable (fun ω => max (F m ω) (0 : ℝ)) P)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (A m ω) (0 : ℝ)) P ∧
      (∫ ω, max (A m ω) (0 : ℝ) ∂P) ≤ ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (B m ω) (0 : ℝ)) P ∧
      (∫ ω, max (B m ω) (0 : ℝ) ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (F m ω) (0 : ℝ)) P ∧
      (∫ ω, max (F m ω) (0 : ℝ) ∂P) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨ka, ha⟩ := hA (ε / 2) hhalf
  obtain ⟨kb, hb⟩ := hB (ε / 2) hhalf
  refine ⟨max ka kb, ?_⟩
  intro m hm
  obtain ⟨hmaI, hma⟩ := ha m ((le_max_left ka kb).trans hm)
  obtain ⟨hmbI, hmb⟩ := hb m ((le_max_right ka kb).trans hm)
  have pointwise (ω) :
      max (F m ω) 0 ≤ max (A m ω) 0 + max (B m ω) 0 := by
    rw [hAB m ω]
    exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have hbnd := integral_mono (hI m) (hmaI.add hmbI) pointwise
  change _ ≤ (∫ ω, max (A m ω) 0 + max (B m ω) 0 ∂P) at hbnd
  rw [integral_add hmaI hmbI] at hbnd
  refine ⟨hI m, ?_⟩
  linarith
