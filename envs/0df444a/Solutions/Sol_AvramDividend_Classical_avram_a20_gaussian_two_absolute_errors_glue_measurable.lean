-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_gaussian_two_absolute_errors_glue_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:51:03.292832+00:00
-- url     : https://prove2.me/submissions/605e2e23-1cd5-4df1-9302-206a33381e66

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
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => S m ω - M m ω - G m ω) P)
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
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨ka, ha⟩ := hA (ε / 2) hhalf
  obtain ⟨kb, hb⟩ := hB (ε / 2) hhalf
  refine ⟨max ka kb, ?_⟩
  intro m hm
  obtain ⟨hmaI, hma⟩ := ha m ((le_max_left ka kb).trans hm)
  obtain ⟨hmbI, hmb⟩ := hb m ((le_max_right ka kb).trans hm)
  have hPnt (ω) : max (S m ω - M m ω - G m ω) 0 ≤
      |A m ω| + |B m ω| := by
    rw [hAB m ω]
    exact max_le
      (add_le_add (le_abs_self _) (le_abs_self _))
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hPosMeas : AEStronglyMeasurable
      (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P :=
    ((hMeas m).aemeasurable.max aemeasurable_const).aestronglyMeasurable
  have hPosI : Integrable
      (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P := by
    apply Integrable.mono' (hmaI.add hmbI) hPosMeas
    filter_upwards [] with ω
    simp only [Pi.add_apply]
    have hNN : 0 ≤ max (S m ω - M m ω - G m ω) (0 : ℝ) :=
      le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hNN]
    exact hPnt ω
  have hBound := integral_mono hPosI (hmaI.add hmbI) hPnt
  simp only [Pi.add_apply] at hBound
  rw [integral_add hmaI hmbI] at hBound
  refine ⟨hPosI, ?_⟩
  linarith
