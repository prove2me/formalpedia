-- Prove2me | solution 1 for DbarRegularity.integral_norm_dbar_sq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T22:23:56.064979+00:00
-- url     : https://prove2.me/submissions/fd6b0ed8-1c76-4853-885d-4e2cba0a3f21

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_integral_norm_dbar_sq_of_innerProductSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory
open scoped ContDiff

theorem integral_norm_dbar_sq_aux {n : ℕ} (φ : ℂ → EuclideanSpace ℂ (Fin n))
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, ‖dbar φ z‖ ^ 2 = (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 :=
  integral_norm_dbar_sq_of_innerProductSpace φ hφ hc

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution {n : ℕ} (φ : ℂ → EuclideanSpace ℂ (Fin n)) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z, ‖dbar φ z‖ ^ 2 = (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 :=
  integral_norm_dbar_sq_aux φ hφ hc
