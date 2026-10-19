-- Prove2me | solution 1 for Ehrhart.BergmanJetSpatialPeriodicity.momentJointTailUpperEnvelope_spatial_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/325a8294-3b63-4d5b-bc3b-863276572d1f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSpatialPeriodicity_momentJointTailSup_spatial_invariant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetSpatialPeriodicity
open Set Function Filter MeasureTheory
open TorusCharacters AdaptedBergmanBasis BergmanMonomials MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic BergmanJetBasis BergmanJetGeodesic BergmanJetRealGeodesic
open BergmanJetUpperEnvelope ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSpatialPeriodicity
open scoped BigOperators Topology
namespace Ehrhart.BergmanJetSpatialPeriodicity
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r
        (sourceJointSpatialDeckHomeomorph m q) =
      momentJointTailUpperEnvelope K F htransport p r q := by
  let h : PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n :=
    sourceJointSpatialDeckHomeomorph m
  have hfun :
      (fun z : PositiveJointLogSpace n =>
        momentJointTailSup K F htransport p r (h z)) =
      momentJointTailSup K F htransport p r := by
    funext z
    exact momentJointTailSup_spatial_invariant
      K F htransport p r m z
  change
    upperRegularization (momentJointTailSup K F htransport p r) (h q) =
      upperRegularization (momentJointTailSup K F htransport p r) q
  rw [← upperRegularization_comp_homeomorph
    (momentJointTailSup K F htransport p r) h q, hfun]
end Ehrhart.BergmanJetSpatialPeriodicity
