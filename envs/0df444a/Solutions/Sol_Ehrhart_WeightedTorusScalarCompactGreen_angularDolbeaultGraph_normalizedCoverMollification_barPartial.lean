-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_normalizedCoverMollification_barPartial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/82817591-4eab-44e7-9682-d36b233dd963

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeakDolbeaultMollification_barPartial_normalizedCoverMollification_eq_of_compact_green
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularDolbeaultGraph_compact_barPartial_green

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
    (k : ℕ) (x : LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (normalizedCoverMollification
        (complexTorusCoverLift (fun q : LogTorus n => f q)) k) x j =
      normalizedCoverMollification
        (complexTorusCoverLift
          (fun q : LogTorus n =>
            (W q : EuclideanSpace ℂ (Fin n)) j)) k x := by
  apply barPartial_normalizedCoverMollification_eq_of_compact_green
    (angularWeightedScalarCoverLift_locallyIntegrable ha f)
  intro ψ hψ hψcompact i
  exact angularDolbeaultGraph_compact_barPartial_green
    ha f W hgraph hψ hψcompact i
end Ehrhart.WeightedTorusScalarCompactGreen
