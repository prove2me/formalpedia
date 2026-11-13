-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:25:17.962206+00:00
-- url     : https://prove2.me/submissions/717dae55-a29b-4316-88f2-9b1452d71765

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Bounded real source marks have compensator integral dominated by
the exact finite original Borel mark intensity. -/
theorem solution
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (f : ℝ → ℝ)
    (hBound : ∀ z ∈ S, |f z| ≤ 1) :
    ‖∫ z in S, f z ∂ν‖ ≤ (ν S).toReal := by
  classical
  letI : IsFiniteMeasure (ν.restrict S) := ⟨by
    simpa using hMass⟩
  have hBoundAE : ∀ᵐ z ∂(ν.restrict S), ‖f z‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    simpa only [Real.norm_eq_abs] using hBound z hz
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := ν.restrict S) hBoundAE
  simpa [Measure.real, measureReal_def] using h
