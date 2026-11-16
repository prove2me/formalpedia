-- Prove2me | solution 1 for AvramDividend.Classical.avram_b26_positive_event_cash_gap_forces_signed_L1_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:31:34.784199+00:00
-- url     : https://prove2.me/submissions/2f62a775-6638-4938-ab81-f68620ed7db8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (F : Ω → ℝ)
    (b δ : ℝ) (hδ : 0 < δ)
    (Err : ℕ → Ω → ℝ)
    (hEI : ∀ n, Integrable (Err n) P)
    (hGap : b + δ ≤ ∫ ω in A, F ω ∂P)
    (hCash : ∀ n, (∫ ω in A, F ω ∂P)
      ≤ b + (∫ ω in A, Err n ω ∂P)) :
    ∀ n, δ ≤ ∫ ω, ‖Err n ω‖ ∂P := by
  intro n
  have hRestrict :
      (∫ ω in A, Err n ω ∂P) ≤ (∫ ω, ‖Err n ω‖ ∂P) := by
    calc
      (∫ ω in A, Err n ω ∂P) ≤
          ‖∫ ω in A, Err n ω ∂P‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ (∫ ω in A, ‖Err n ω‖ ∂P) :=
        norm_integral_le_integral_norm (μ := P.restrict A) (f := Err n)
      _ ≤ (∫ ω, ‖Err n ω‖ ∂P) := by
        apply integral_mono_measure (Measure.restrict_le_self)
        · filter_upwards [] with ω
          exact norm_nonneg _
        · exact (hEI n).norm
  linarith [hGap, hCash n, hRestrict]
