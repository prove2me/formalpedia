-- Prove2me | solution 1 for Ehrhart.BergmanJetSpatialPeriodicity.momentJointTailSup_spatial_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/134d9db2-3771-48c2-998c-2d784b36c7a7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSpatialPeriodicity_momentPositiveJointGeodesic_spatial_invariant

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
    momentJointTailSup K F htransport p r
        (sourceJointSpatialDeckHomeomorph m q) =
      momentJointTailSup K F htransport p r q := by
  unfold momentJointTailSup
  have hfun :
      (fun j : ℕ =>
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r + j)
          (sourceJointSpatialDeckHomeomorph m q)) =
      (fun j : ℕ =>
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r + j) q) := by
    funext j
    exact momentPositiveJointGeodesic_spatial_invariant
      K F htransport p _ m q
  rw [hfun]
end Ehrhart.BergmanJetSpatialPeriodicity
