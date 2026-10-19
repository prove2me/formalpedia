-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifiedRootBochner.sourceTorusFormExteriorDerivativeDensity_cutoff_eq_antisymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/fa01cd67-ae7d-419c-8ede-206cff33d6fe

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusNoncompactBochner_sourceTorusBarPartial_cutoffPhysicalField_antisymmetric

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusClosedMollifiedRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open WeightedTorusBrascampLieb TorusNoncompactBochner TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusClosedMollifiedRootBochner
theorem _root_.solution
    {n : ℕ} {V : LogSpace n → LogSpace n}
    (hV : ContDiff ℝ 2 V)
    (hclosed : ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial (fun z => V z i) j q))
    (m : ℕ) (q : LogTorus n) :
    sourceTorusFormExteriorDerivativeDensity
        (cutoffPhysicalField m V) q =
      complexEuclideanAntisymmetricEnergy
        (sourceCutoffDerivativeCommutator m V q) := by
  unfold sourceTorusFormExteriorDerivativeDensity
    complexEuclideanAntisymmetricEnergy
  simp_rw [sourceTorusBarPartial_cutoffPhysicalField_antisymmetric
    hV hclosed m]
end Ehrhart.TorusClosedMollifiedRootBochner
