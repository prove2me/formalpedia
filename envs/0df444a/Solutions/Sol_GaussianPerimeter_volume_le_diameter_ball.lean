-- Prove2me | solution 1 for GaussianPerimeter.volume_le_diameter_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:43:59.435427+00:00
-- url     : https://prove2.me/submissions/fadbee00-b61c-437d-b74d-18ac72cbf058

module
public import Definitions.Def_GaussianPerimeter_BrunnMinkowski
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Definitions.Def_GaussianPerimeter_HausdorffNormalization
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_brunn_minkowski_euclideanSpace


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Metric
open scoped ENNReal Pointwise
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : IsCompact A) :
    (2 : ℝ≥0∞) ^ (n + 1) * volume A ≤
      volume (closedBall 0 (diam A) : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsum := hA.add hA.neg
  have hneg : volume (-A) = volume A := by
    have hsmul : (-1 : ℝ) • A = -A := by
      rw [← Set.image_smul, ← Set.image_neg_eq_neg]
      simp
    rw [← hsmul, Measure.addHaar_smul]
    simp
  have h := VolumeComparison.brunn_minkowski_euclideanSpace hne hA.measurableSet
    hne.neg hA.neg.measurableSet hsum.measurableSet
  rw [hneg, ← two_mul] at h
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have h' := (ENNReal.le_rpow_inv_iff hd).mp h
  rw [ENNReal.mul_rpow_of_nonneg _ _ hd.le, ENNReal.rpow_inv_rpow hd.ne',
    ← Nat.cast_succ, ENNReal.rpow_natCast] at h'
  refine h'.trans (measure_mono ?_)
  rintro x ⟨y, hy, z, hz, rfl⟩
  rw [mem_closedBall, dist_zero_right]
  rw [mem_neg] at hz
  simpa only [dist_eq_norm, sub_neg_eq_add] using
    dist_le_diam_of_mem hA.isBounded hy hz
end GaussianPerimeter
