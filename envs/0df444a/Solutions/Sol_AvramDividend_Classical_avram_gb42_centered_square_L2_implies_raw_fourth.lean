-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb42_centered_square_L2_implies_raw_fourth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:33:49.5142+00:00
-- url     : https://prove2.me/submissions/7bb6387a-b407-4dd8-bd69-c0acc174f72b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical

/-- The centred quadratic L2 moment dominates the raw fourth moment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (a : ℝ) (hZ : Measurable Z)
    (hc : Integrable (fun ω => ((Z ω) ^ 2 - a) ^ 2) P) :
    Integrable (fun ω => (Z ω) ^ 4) P ∧
      (∫ ω, (Z ω) ^ 4 ∂P) ≤
        2 * ((∫ ω, ((Z ω) ^ 2 - a) ^ 2 ∂P) + a ^ 2) := by
  have hmeas : Measurable (fun ω => (Z ω) ^ 4) := hZ.pow_const 4
  have hmajor : Integrable (fun ω =>
      2 * (((Z ω) ^ 2 - a) ^ 2 + a ^ 2)) P := by
    exact (hc.add (integrable_const _)).const_mul 2
  have hpoint (ω : Ω) :
      (Z ω) ^ 4 ≤ 2 * (((Z ω) ^ 2 - a) ^ 2 + a ^ 2) := by
    nlinarith [sq_nonneg ((Z ω) ^ 2 - 2 * a)]
  have hi : Integrable (fun ω => (Z ω) ^ 4) P := by
    apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (Z ω) ^ 4)]
    exact hpoint ω
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, (Z ω) ^ 4 ∂P) ≤
        ∫ ω, 2 * (((Z ω) ^ 2 - a) ^ 2 + a ^ 2) ∂P :=
      integral_mono hi hmajor hpoint
    _ = 2 * ((∫ ω, ((Z ω) ^ 2 - a) ^ 2 ∂P) + a ^ 2) := by
      rw [integral_const_mul, integral_add hc (integrable_const _)]
      simp
