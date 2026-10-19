-- Prove2me | solution 1 for Ehrhart.BergmanJetEnvelopeLimit.tendsto_momentJointTailUpperEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/ba1723bb-3c59-4aa9-8a9a-7e2637a83215

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_momentJointTailUpperEnvelope_antitone

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetEnvelopeLimit
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopePlurisubharmonic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetEnvelopeLimit
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    Tendsto
      (fun r : ℕ => momentJointTailUpperEnvelope
        K F htransport p r q)
      atTop (𝓝 (momentJointUpperEnvelope
        K F htransport p q)) :=
  tendsto_atTop_ciInf
    (fun _ _ hrs => momentJointTailUpperEnvelope_antitone
      K F htransport p hrs q)
    (momentJointTailUpperEnvelope_bddBelow
      K F htransport p q)
end Ehrhart.BergmanJetEnvelopeLimit
