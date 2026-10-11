-- Prove2me | solution 1 for BlackScholesModel.gaussianReal_Iic_eq_stdNormalCDF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:32:45.9767+00:00
-- url     : https://prove2.me/submissions/d1247ea3-83ec-4554-8b49-4751156b14f5

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The standard Gaussian half-line measure is the standard normal CDF. -/
theorem solution (x : ℝ) :
    (gaussianReal 0 1).real (Set.Iic x) = stdNormalCDF x := by
  have hPDF (z : ℝ) :
      gaussianPDFReal 0 (1 : NNReal) z =
        (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-z ^ 2 / 2) := by
    simp [ProbabilityTheory.gaussianPDFReal_def]
  have hnonneg : 0 ≤
      ∫ z in Set.Iic x, gaussianPDFReal 0 (1 : NNReal) z := by
    apply integral_nonneg
    intro z
    exact ProbabilityTheory.gaussianPDFReal_nonneg 0 1 z
  change ((gaussianReal 0 (1 : NNReal)) (Set.Iic x)).toReal =
      stdNormalCDF x
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral
    (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0) (Set.Iic x)]
  rw [ENNReal.toReal_ofReal hnonneg]
  unfold stdNormalCDF
  simp_rw [hPDF]
  rw [MeasureTheory.integral_const_mul]