-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger143_measurable_residual_two_absolute_L1_errors_glue_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:36:07.077085+00:00
-- url     : https://prove2.me/submissions/40cffb03-663c-4a37-aeb4-2bfb81e06d02

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
    (hI : ∀ m : ℕ, Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧
      (∫ ω, |A m ω| ∂P) ≤ ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |B m ω|) P ∧
      (∫ ω, |B m ω| ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨ka, ha⟩ := hA (ε / 2) (half_pos hε)
  obtain ⟨kb, hb⟩ := hB (ε / 2) (half_pos hε)
  refine ⟨max ka kb, ?_⟩
  intro m hm
  obtain ⟨haI, haε⟩ := ha m (le_trans (le_max_left ka kb) hm)
  obtain ⟨hbI, hbε⟩ := hb m (le_trans (le_max_right ka kb) hm)
  have hbound : ∀ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ≤
      |A m ω| + |B m ω| := by
    intro ω
    rw [hAB m ω]
    exact max_le_iff.mpr
      ⟨le_trans (le_abs_self _) (abs_add_le _ _),
       add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
  refine ⟨hI m, ?_⟩
  calc
    (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤
        ∫ ω, (|A m ω| + |B m ω|) ∂P :=
          integral_mono (hI m) (haI.add hbI) hbound
    _ = (∫ ω, |A m ω| ∂P) + (∫ ω, |B m ω| ∂P) :=
      integral_add haI hbI
    _ ≤ ε := by linarith
