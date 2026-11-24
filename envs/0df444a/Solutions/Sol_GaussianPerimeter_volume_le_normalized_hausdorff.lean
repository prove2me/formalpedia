-- Prove2me | solution 1 for GaussianPerimeter.volume_le_normalized_hausdorff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:53:31.575872+00:00
-- url     : https://prove2.me/submissions/1f059ad5-04de-4a94-8e7b-17aae6253a07

module
public import Definitions.Def_GaussianPerimeter_BrunnMinkowski
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Definitions.Def_GaussianPerimeter_HausdorffNormalization
public import Theorems.Thm_GaussianPerimeter_volume_le_diameter_ball

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Metric
open scoped ENNReal Pointwise
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) / (2 : ℝ≥0∞) ^ (n + 1)) •
        μH[((n + 1 : ℕ) : ℝ)] := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let C : ℝ≥0∞ := volume (ball (0 : E) 1) / (2 : ℝ≥0∞) ^ (n + 1)
  have hC0 : C ≠ 0 := (ENNReal.div_pos (measure_ball_pos volume 0 zero_lt_one).ne'
    (by simp)).ne'
  have hCtop : C ≠ ⊤ := ENNReal.div_ne_top measure_ball_ne_top (by positivity)
  have hbound {A : Set E} (hA : Bornology.IsBounded A) :
      volume A ≤ C * (ediam A) ^ (n + 1) := by
    have hcl : IsCompact (closure A) :=
      isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hA.closure⟩
    have h := volume_le_diameter_ball hcl
    rw [diam_closure, Measure.addHaar_closedBall volume 0 diam_nonneg,
      finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow diam_nonneg,
      Metric.diam, ENNReal.ofReal_toReal hA.ediam_ne_top] at h
    have h2 : (2 : ℝ≥0∞) ^ (n + 1) ≠ 0 := by positivity
    have h2' : (2 : ℝ≥0∞) ^ (n + 1) ≠ ⊤ := by simp
    have hclbound : volume (closure A) ≤
        ((ediam A) ^ (n + 1) * volume (ball (0 : E) 1)) / (2 : ℝ≥0∞) ^ (n + 1) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl h2) (Or.inl h2')).mpr
      rw [mul_comm (volume (closure A))]
      exact h
    exact (measure_mono subset_closure).trans (by
      simpa only [C, div_eq_mul_inv, mul_right_comm, mul_comm, mul_left_comm] using hclbound)
  have hraw : C⁻¹ • (volume : Measure E) ≤ μH[((n + 1 : ℕ) : ℝ)] := by
    apply Measure.le_hausdorffMeasure _ _ 1 zero_lt_one
    intro A hA
    have hb : Bornology.IsBounded A :=
      isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top (by simp) hA)
    have hh := mul_le_mul_right (hbound hb) C⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul] at hh
    simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast] using hh
  change (volume : Measure E) ≤ C • μH[((n + 1 : ℕ) : ℝ)]
  intro A
  change volume A ≤ C * μH[((n + 1 : ℕ) : ℝ)] A
  calc
    volume A = C * (C⁻¹ * volume A) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
    _ ≤ C * μH[((n + 1 : ℕ) : ℝ)] A := mul_le_mul_right (hraw A) C
end GaussianPerimeter
