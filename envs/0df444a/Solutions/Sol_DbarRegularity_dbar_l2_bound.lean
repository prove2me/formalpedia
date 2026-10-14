-- Prove2me | solution 1 for DbarRegularity.dbar_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:11:28.595188+00:00
-- url     : https://prove2.me/submissions/a481056a-cccd-4d8f-9123-9c7fd874c823

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_integral_norm_dbar_sq
import Theorems.Thm_DbarRegularity_integral_norm_sq_le_integral_norm_fderiv_one_sq
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem dbar_l2_bound_aux {n : ℕ} (R : ℝ) (φ : ℂ → EuclideanSpace ℂ (Fin n))
    (hφ : ContDiff ℝ ∞ φ) (hsupp : tsupport φ ⊆ ball 0 R) :
    (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + (∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2) + (∫ z, ‖φ z‖ ^ 2)
      ≤ (4 * R ^ 2 + 1) * ∫ z, ‖dbar φ z‖ ^ 2 := by
  have hc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans ball_subset_closedBall)
  have h1 := integral_norm_dbar_sq φ hφ hc
  have h2 := integral_norm_sq_le_integral_norm_fderiv_one_sq R φ
    (hφ.of_le (by exact_mod_cast le_top)) hsupp
  have h3 : 0 ≤ ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 := integral_nonneg fun _ => by positivity
  rw [h1]
  nlinarith [mul_nonneg (sq_nonneg R) h3]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution {n : ℕ} (R : ℝ) (φ : ℂ → EuclideanSpace ℂ (Fin n))
    (hφ : ContDiff ℝ ∞ φ) (hsupp : tsupport φ ⊆ ball 0 R) :
    (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + (∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2) + (∫ z, ‖φ z‖ ^ 2)
      ≤ (4 * R ^ 2 + 1) * ∫ z, ‖dbar φ z‖ ^ 2 :=
  dbar_l2_bound_aux R φ hφ hsupp
