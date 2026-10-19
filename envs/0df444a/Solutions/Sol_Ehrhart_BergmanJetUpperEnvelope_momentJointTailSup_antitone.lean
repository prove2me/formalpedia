-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperEnvelope.momentJointTailSup_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/32ee63e6-95d7-491f-947e-b6fbeca981ba

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetUpperEnvelope
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetGeodesic BergmanJetRealGeodesic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetUpperEnvelope
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {r s : ℕ} (hrs : r ≤ s)
    (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p s q ≤
      momentJointTailSup K F htransport p r q := by
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  apply le_csSup
    (momentJointTailSup_range_bddAbove
      K F htransport p r q)
  have hindex :
      momentJointTailStart K F htransport p + r +
        (s - r + j) =
      momentJointTailStart K F htransport p + s + j := by
    omega
  refine ⟨s - r + j, ?_⟩
  change
    momentPositiveJointGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r +
        (s - r + j)) q =
    momentPositiveJointGeodesic K F htransport p
      (momentJointTailStart K F htransport p + s + j) q
  rw [hindex]
end Ehrhart.BergmanJetUpperEnvelope
