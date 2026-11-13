-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_real_source_centered_square_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:47:18.647273+00:00
-- url     : https://prove2.me/submissions/f1823963-a2cb-4fab-b5f6-f433ef5b14a4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (r v : ℝ)
    (hY : Integrable Y P)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P)
    (hZero : (∫ ω, Y ω ∂P) = 0)
    (hVariance : (∫ ω, (Y ω) ^ 2 ∂P) = v) :
    Integrable (fun ω => (Y ω + r) ^ 2) P ∧
      (∫ ω, (Y ω + r) ^ 2 ∂P) = v + r ^ 2 := by
  have hCross : Integrable (fun ω => (2 * r) * Y ω) P :=
    hY.const_mul (2 * r)
  have hSum : Integrable (fun ω => (Y ω) ^ 2 + (2 * r) * Y ω) P :=
    hY2.add hCross
  have hEq : (fun ω => (Y ω + r) ^ 2) =
      (fun ω => (Y ω) ^ 2 + (2 * r) * Y ω + r ^ 2) := by
    funext ω
    ring
  constructor
  · rw [hEq]
    exact hSum.add (integrable_const (r ^ 2))
  · rw [hEq, integral_add hSum (integrable_const (r ^ 2))]
    rw [integral_add hY2 hCross]
    rw [integral_const_mul]
    simp only [integral_const, measure_univ, one_smul]
    rw [hZero, hVariance]
    simp [MeasureTheory.Measure.real_def]
