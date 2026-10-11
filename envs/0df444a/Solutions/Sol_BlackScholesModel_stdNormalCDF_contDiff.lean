-- Prove2me | solution 1 for BlackScholesModel.stdNormalCDF_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:36:13.147415+00:00
-- url     : https://prove2.me/submissions/88cb0c3b-c09e-48cf-9235-f27b1c2bd1e2

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_hasDerivAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The normal density is smooth, so its primitive is smooth. -/
theorem solution : ContDiff ℝ ∞ stdNormalCDF := by
  have hpdf : ContDiff ℝ ∞ stdNormalPDF := by
    unfold stdNormalPDF
    fun_prop
  have hdiff : Differentiable ℝ stdNormalCDF := by
    intro x
    exact (stdNormalCDF_hasDerivAt x).differentiableAt
  have heq : deriv stdNormalCDF = stdNormalPDF := by
    funext x
    exact (stdNormalCDF_hasDerivAt x).deriv
  exact (contDiff_infty_iff_deriv).2 ⟨hdiff, by simpa only [heq] using hpdf⟩
