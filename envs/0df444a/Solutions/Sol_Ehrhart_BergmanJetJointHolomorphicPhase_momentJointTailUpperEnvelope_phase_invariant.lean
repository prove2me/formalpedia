-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhase.momentJointTailUpperEnvelope_phase_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/f96ffb88-9545-4cca-a1ba-273935713ec9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhase_momentJointTailSup_phase_invariant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicPhase
open Set Function Filter MeasureTheory
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization
open ActualJetUpperEnvelope JetEnvelopeRightDerivative JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetJointHolomorphicPhase
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r
        (sourceJointPhaseHomeomorph u hu q) =
      momentJointTailUpperEnvelope K F htransport p r q := by
  let h : PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n :=
    sourceJointPhaseHomeomorph (n := n) u hu
  have hfun :
      (fun z : PositiveJointLogSpace n =>
        momentJointTailSup K F htransport p r (h z)) =
        momentJointTailSup K F htransport p r := by
    funext z
    exact momentJointTailSup_phase_invariant
      K F htransport p r u hu z
  change
    upperRegularization
        (momentJointTailSup K F htransport p r) (h q) =
      upperRegularization
        (momentJointTailSup K F htransport p r) q
  rw [← upperRegularization_comp_homeomorph
    (momentJointTailSup K F htransport p r) h q, hfun]
end Ehrhart.BergmanJetJointHolomorphicPhase
