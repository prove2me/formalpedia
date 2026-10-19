-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousSmoothRootBochner.angularClosedGraphMollifiedRootBochner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/055bc131-2911-4723-ad92-6363f5b4b86d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_sourceTorusClosedForm_angularGraphMollifiedPhysicalField
import Theorems.Thm_Ehrhart_TorusClosedMollifiedRootBochner_sourceTorusFormExteriorDerivativeDensity_cutoff_eq_antisymmetric
import Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousSmoothRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph
open RadialPhysicalInverseSquareRootEnergy TorusRootCurvatureCoercivity TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusMollifiedBochner TorusWeakRadialExteriorEnergy
open TorusClosedMollifiedRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousSmoothRootBochner
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (ℓ m : ℕ) :
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      complexEuclideanAntisymmetricEnergy
        (sourceCutoffDerivativeCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q)
      ∂(angularWeightedTorusMeasure a)).re := by
  have hV : ContDiff ℝ 2
      (angularGraphMollifiedPhysicalField W ℓ) :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp := angularGraphMollifiedPhysicalField_periodic W ℓ
  have hclosed :=
    WeightedTorusScalarCompactGreen.sourceTorusClosedForm_angularGraphMollifiedPhysicalField
      ha f W hgraph ℓ
  have hbochner :=
    angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
      ha ha2 hH
      (angularGraphMollifiedPhysicalField W ℓ) hV hp m
  change
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤ _ at hbochner
  simpa only
    [sourceTorusFormExteriorDerivativeDensity_cutoff_eq_antisymmetric
      hV hclosed m] using hbochner
end Ehrhart.TorusHomogeneousSmoothRootBochner
