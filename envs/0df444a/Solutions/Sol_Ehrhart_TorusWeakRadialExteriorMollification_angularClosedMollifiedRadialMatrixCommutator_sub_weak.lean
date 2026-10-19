-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorMollification.angularClosedMollifiedRadialMatrixCommutator_sub_weak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/4a514f70-7118-470a-aa2d-74d3d02f80b5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakRadialExteriorMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedPoincare WeightedBrascampLieb
open WeightedResolventConstantCore EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open TorusMollifiedBochner TorusNoncompactBochner TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusWeakRadialExteriorMollification
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    sourceCutoffDerivativeCommutator m
        (angularGraphMollifiedPhysicalField W ℓ) q -
      angularWeakSourceCutoffDerivativeCommutator W m q =
      complexEuclideanOuterProduct
        (torusFormRepresentative
          (angularGraphMollifiedPhysicalField W ℓ) q - W q)
        (sourceCutoffBarGradient m q) := by
  rw [sourceCutoffDerivativeCommutator_eq_outerProduct]
  unfold angularWeakSourceCutoffDerivativeCommutator
  ext ij
  change
    (torusFormRepresentative
        (angularGraphMollifiedPhysicalField W ℓ) q) ij.1 *
        (sourceCutoffBarGradient m q) ij.2 -
      (W q) ij.1 * (sourceCutoffBarGradient m q) ij.2 =
      ((torusFormRepresentative
          (angularGraphMollifiedPhysicalField W ℓ) q) ij.1 -
        (W q) ij.1) * (sourceCutoffBarGradient m q) ij.2
  ring
end Ehrhart.TorusWeakRadialExteriorMollification
