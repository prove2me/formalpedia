-- Prove2me | solution 1 for Ehrhart.TorusNoncompactBochner.angularTorus_compact_form_curvature_le_adjoint_add_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/fa9adabc-9548-47ce-9ee3-ed18342d2683

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCore_sourceTorusFormFullDerivativeDensity_re_nonneg
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormFullDerivativeDensity
import Theorems.Thm_Ehrhart_WeightedTorusBochner_angularTorus_weighted_complex_dolbeault_form_bochner_identity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.TorusNoncompactBochner
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p
        ∂(angularWeightedTorusMeasure a)).re ≤
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
          ∂(angularWeightedTorusMeasure a)).re +
    (∫ p : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity W p
        ∂(angularWeightedTorusMeasure a)).re := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  have hfull : Integrable
      (sourceTorusFormFullDerivativeDensity W) μ :=
    integrable_angularTorusFormFullDerivativeDensity
      W ha hW hWp hWc
  have hfull_nonneg :
      0 ≤ (∫ p : LogTorus n,
        sourceTorusFormFullDerivativeDensity W p ∂μ).re := by
    change 0 ≤ RCLike.re
      (∫ p : LogTorus n,
        sourceTorusFormFullDerivativeDensity W p ∂μ)
    rw [← integral_re hfull]
    exact MeasureTheory.integral_nonneg
      (fun p => sourceTorusFormFullDerivativeDensity_re_nonneg W p)
  have hboch :=
    angularTorus_weighted_complex_dolbeault_form_bochner_identity
      W ha ha2 hW hWp hWc
  have hre := congrArg Complex.re hboch
  simp only [Complex.add_re] at hre
  change
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p ∂μ).re ≤
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p) ∂μ).re +
    (∫ p : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity W p ∂μ).re
  linarith
end Ehrhart.TorusNoncompactBochner
