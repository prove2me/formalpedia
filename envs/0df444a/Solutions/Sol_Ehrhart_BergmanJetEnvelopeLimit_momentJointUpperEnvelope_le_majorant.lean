-- Prove2me | solution 1 for Ehrhart.BergmanJetEnvelopeLimit.momentJointUpperEnvelope_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/2ef145f2-7e25-4075-90ba-43c4fb764ace

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_eventually_momentJointTailUpperEnvelope_le_majorant_add

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
    momentJointUpperEnvelope K F htransport p q ≤
      momentJointMajorant K F q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr⟩ :=
    (eventually_momentJointTailUpperEnvelope_le_majorant_add
      K F htransport p hε).exists
  calc
    momentJointUpperEnvelope K F htransport p q ≤
      momentJointTailUpperEnvelope
        K F htransport p r q :=
      ciInf_le (momentJointTailUpperEnvelope_bddBelow
        K F htransport p q) r
    _ ≤ momentJointMajorant K F q + ε := hr q
end Ehrhart.BergmanJetEnvelopeLimit
