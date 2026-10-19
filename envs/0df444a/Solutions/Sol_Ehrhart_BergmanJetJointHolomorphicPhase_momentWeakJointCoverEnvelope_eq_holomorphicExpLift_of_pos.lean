-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhase.momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/55a276f4-a68d-4fd9-abef-58391509eb19

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonic_sourceJointExpPositiveLift_eq_phase_radialLift
import Theorems.Thm_Ehrhart_BergmanJetJointEnvelopeRegularization_momentWeakJointCoverEnvelope_of_positive
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhase_momentJointUpperEnvelope_phase_invariant

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
    (p : LogSpace n) (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourceJointExpPositiveLift q hq) := by
  let u : ℂ := Complex.exp ((q.2.im : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := sourceJointAuxiliaryPhase_norm q.2
  have hrad := momentWeakJointCoverEnvelope_of_positive
    K F htransport p q hq
  rw [sourceJointExpPositiveLift_eq_phase_radialLift]
  exact hrad.trans
    (momentJointUpperEnvelope_phase_invariant
      K F htransport p u hu
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq)).symm
end Ehrhart.BergmanJetJointHolomorphicPhase
