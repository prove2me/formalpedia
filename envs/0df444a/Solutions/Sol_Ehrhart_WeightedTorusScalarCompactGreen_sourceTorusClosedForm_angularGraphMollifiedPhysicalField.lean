-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.sourceTorusClosedForm_angularGraphMollifiedPhysicalField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/2b7f8882-789a-4852-a92d-aead0d2dea78

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusMollifiedBochner_sourceTorusClosedForm_barPartial
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularDolbeaultGraph_normalizedCoverMollification_barPartial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusScalarCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold
namespace Ehrhart.WeightedTorusScalarCompactGreen
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (k : ℕ) :
    ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        MatrixTorusBochnerIdentity.sourceTorusBarPartial
          (fun z => angularGraphMollifiedPhysicalField W k z i) j q) := by
  let F : LogSpace n → ℂ :=
    normalizedCoverMollification
      (complexTorusCoverLift (fun q : LogTorus n => f q)) k
  have hF : ContDiff ℝ 2 F :=
    contDiff_normalizedCoverMollification
      (angularWeightedScalarCoverLift_locallyIntegrable ha f) k 2
  have hident (z : LogSpace n) (i : Fin n) :
      barPartialCoordinate F z i =
        angularGraphMollifiedPhysicalField W k z i :=
    angularDolbeaultGraph_normalizedCoverMollification_barPartial
      ha f W hgraph k z i
  have hclosed := sourceTorusClosedForm_barPartial hF
  intro q
  apply Matrix.IsSymm.ext
  intro i j
  have hi :
      (fun z => angularGraphMollifiedPhysicalField W k z i) =
        (fun z => barPartialCoordinate F z i) := by
    funext z
    exact (hident z i).symm
  have hj :
      (fun z => angularGraphMollifiedPhysicalField W k z j) =
        (fun z => barPartialCoordinate F z j) := by
    funext z
    exact (hident z j).symm
  rw [hj, hi]
  exact (hclosed q).apply i j
end Ehrhart.WeightedTorusScalarCompactGreen
