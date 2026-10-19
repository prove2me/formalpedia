-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperEnvelope.eventually_momentJointTailUpperEnvelope_le_majorant_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/9f88a636-6a71-4ab2-8d05-fe91a4039056

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_eventually_momentJointTailSup_le_majorant_add

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
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ q : PositiveJointLogSpace n,
      momentJointTailUpperEnvelope K F htransport p r q ≤
        momentJointMajorant K F q + ε := by
  filter_upwards
    [eventually_momentJointTailSup_le_majorant_add
      K F htransport p hε] with r hr q
  exact upperRegularization_le_of_continuous_majorant
    (momentJointTailSup K F htransport p r)
    (fun z => momentJointMajorant K F z + ε)
    ((continuous_momentJointMajorant K F).add continuous_const)
    hr q
end Ehrhart.BergmanJetUpperEnvelope
