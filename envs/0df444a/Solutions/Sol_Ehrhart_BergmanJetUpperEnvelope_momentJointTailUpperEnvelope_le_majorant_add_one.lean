-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperEnvelope.momentJointTailUpperEnvelope_le_majorant_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/5d830ec7-42e5-4834-85ed-60812d35d264

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
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r q ≤
      momentJointMajorant K F q + 1 :=
  upperRegularization_le_of_continuous_majorant
    (momentJointTailSup K F htransport p r)
    (fun z => momentJointMajorant K F z + 1)
    ((continuous_momentJointMajorant K F).add continuous_const)
    (momentJointTailSup_le_majorant_add_one
      K F htransport p r) q
end Ehrhart.BergmanJetUpperEnvelope
