-- Prove2me | solution 1 for GaussianPerimeter.gaussianPerimeter_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:42.109688+00:00
-- url     : https://prove2.me/submissions/4e045cf9-edc5-4be4-8324-39fe0bae3e76

module
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Definitions.Def_GaussianPerimeter_Definitions

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin (k + 1)))) :
    gaussianPerimeter K =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) / (2 : ℝ≥0∞) ^ k) *
        (∫⁻ x in frontier K, ENNReal.ofReal
          ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)) ∂μH[(k : ℝ)]) := by
  unfold gaussianPerimeter
  rfl
end GaussianPerimeter
