-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a25_positive_l1_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:18:42.14689+00:00
-- url     : https://prove2.me/submissions/27ba0eb8-5e3d-412f-a436-4e445af01ad9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S M G A B : ℕ → Ω → ℝ)
    (hAB : ∀ m ω, S m ω - M m ω - G m ω = A m ω + B m ω)
    (hI : ∀ m, Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧ (∫ ω, |A m ω| ∂P) ≤ ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (B m ω) 0) P ∧
      (∫ ω, max (B m ω) 0 ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤ ε := by
  intro ε hε; have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨ka, ha⟩ := hA (ε / 2) hhalf; obtain ⟨kb, hb⟩ := hB (ε / 2) hhalf
  refine ⟨max ka kb, ?_⟩; intro m hm
  obtain ⟨hmaI, hma⟩ := ha m ((le_max_left ka kb).trans hm)
  obtain ⟨hmbI, hmb⟩ := hb m ((le_max_right ka kb).trans hm)
  have pointwise (ω) : max (S m ω - M m ω - G m ω) 0 ≤
      |A m ω| + max (B m ω) 0 := by
    rw [hAB m ω]
    exact max_le (add_le_add (le_abs_self _) (le_max_left _ _))
      (add_nonneg (abs_nonneg _) (le_max_right _ _))
  have hbnd := integral_mono (hI m) (hmaI.add hmbI) pointwise
  change _ ≤ (∫ ω, |A m ω| + max (B m ω) 0 ∂P) at hbnd
  rw [integral_add hmaI hmbI] at hbnd; refine ⟨hI m, ?_⟩
  linarith
