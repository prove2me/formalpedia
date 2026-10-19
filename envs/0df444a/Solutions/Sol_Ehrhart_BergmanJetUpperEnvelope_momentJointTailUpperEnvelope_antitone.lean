-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperEnvelope.momentJointTailUpperEnvelope_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/5e820472-c228-4e2c-a066-a040e34c10da

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_momentJointTailSup_antitone

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
    momentJointTailUpperEnvelope K F htransport p s q ≤
      momentJointTailUpperEnvelope K F htransport p r q :=
  upperRegularization_mono
    (momentJointTailSup K F htransport p s)
    (momentJointTailSup K F htransport p r) q
    (momentJointTailSup_antitone K F htransport p hrs)
    (momentJointTailSup_localUpperBounds_nonempty
      K F htransport p r q)
end Ehrhart.BergmanJetUpperEnvelope
