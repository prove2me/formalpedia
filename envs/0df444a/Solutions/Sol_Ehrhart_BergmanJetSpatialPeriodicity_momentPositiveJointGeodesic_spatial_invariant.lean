-- Prove2me | solution 1 for Ehrhart.BergmanJetSpatialPeriodicity.momentPositiveJointGeodesic_spatial_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/db914aba-dcb6-430c-a4dd-1d9af9b605f3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeSpatialPeriodicity_sourceJointSpatialDeckHomeomorph_spatial
import Theorems.Thm_Ehrhart_EnvelopeSpatialPeriodicity_jointLogTime_sourceJointSpatialDeckHomeomorph

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
    (p : LogSpace n) (k : ℕ) (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k
        (sourceJointSpatialDeckHomeomorph m q) =
      momentPositiveJointGeodesic K F htransport p k q := by
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
    momentPositiveJointGeodesic_eq_momentJetGeodesic,
    sourceJointSpatialDeckHomeomorph_spatial,
    jointLogTime_sourceJointSpatialDeckHomeomorph]
  exact momentJetGeodesic_spatial_periodic
    K (Nat.zero_lt_succ k) F htransport p
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) (jointLogTime q) m q.val.1
end Ehrhart.BergmanJetSpatialPeriodicity
