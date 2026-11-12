-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb38_bounded_quadratic_fourth_to_integrable_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:27:04.994634+00:00
-- url     : https://prove2.me/submissions/f021dfc0-86b9-4e3e-8dfd-911861169e82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

/-- Bounded coefficients transfer a fourth moment to a quadratic L2 bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H Z : Ω → ℝ) (a B K : ℝ)
    (hH : Measurable H) (hZ : Measurable Z)
    (hK : 0 ≤ K) (hHb : ∀ ω, |H ω| ≤ K)
    (hZ4 : Integrable (fun ω => (Z ω) ^ 4) P)
    (hB : (∫ ω, (Z ω) ^ 4 ∂P) ≤ B) :
    Integrable (fun ω => (H ω * ((Z ω) ^ 2 - a)) ^ 2) P ∧
      (∫ ω, (H ω * ((Z ω) ^ 2 - a)) ^ 2 ∂P) ≤
        2 * K ^ 2 * (B + a ^ 2) := by
  have hmeas : Measurable (fun ω =>
      (H ω * ((Z ω) ^ 2 - a)) ^ 2) :=
    (hH.mul ((hZ.pow_const 2).sub_const a)).pow_const 2
  have hmajor : Integrable (fun ω =>
      2 * K ^ 2 * ((Z ω) ^ 4 + a ^ 2)) P := by
    exact (hZ4.add (integrable_const _)).const_mul (2 * K ^ 2)
  have hpoint (ω : Ω) :
      (H ω * ((Z ω) ^ 2 - a)) ^ 2 ≤
        2 * K ^ 2 * ((Z ω) ^ 4 + a ^ 2) := by
    have ha : |H ω| ≤ K := hHb ω
    have hh : (H ω) ^ 2 ≤ K ^ 2 := by
      nlinarith [sq_nonneg (K - |H ω|),
        sq_abs (H ω), abs_nonneg (H ω)]
    have hz : ((Z ω) ^ 2 - a) ^ 2 ≤
        2 * ((Z ω) ^ 4 + a ^ 2) := by
      nlinarith [sq_nonneg ((Z ω) ^ 2 + a)]
    calc
      _ = (H ω) ^ 2 * ((Z ω) ^ 2 - a) ^ 2 := by ring
      _ ≤ K ^ 2 * ((Z ω) ^ 2 - a) ^ 2 :=
        mul_le_mul_of_nonneg_right hh (sq_nonneg _)
      _ ≤ K ^ 2 * (2 * ((Z ω) ^ 4 + a ^ 2)) :=
        mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = 2 * K ^ 2 * ((Z ω) ^ 4 + a ^ 2) := by ring
  have hInt : Integrable (fun ω =>
      (H ω * ((Z ω) ^ 2 - a)) ^ 2) P := by
    apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  refine ⟨hInt, ?_⟩
  calc
    (∫ ω, (H ω * ((Z ω) ^ 2 - a)) ^ 2 ∂P) ≤
        ∫ ω, 2 * K ^ 2 * ((Z ω) ^ 4 + a ^ 2) ∂P :=
      integral_mono hInt hmajor hpoint
    _ = 2 * K ^ 2 * ((∫ ω, (Z ω) ^ 4 ∂P) + a ^ 2) := by
      rw [integral_const_mul, integral_add hZ4 (integrable_const _)]
      simp
    _ ≤ 2 * K ^ 2 * (B + a ^ 2) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity
