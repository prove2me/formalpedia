-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhase.momentJointUpperEnvelope_phase_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/767a07f9-aaff-4174-a432-d1358aad33c2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhase_momentJointTailUpperEnvelope_phase_invariant

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
    (p : LogSpace n) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentJointUpperEnvelope K F htransport p
        (sourceJointPhaseHomeomorph u hu q) =
      momentJointUpperEnvelope K F htransport p q := by
  unfold momentJointUpperEnvelope
  congr 1
  funext r
  exact momentJointTailUpperEnvelope_phase_invariant
    K F htransport p r u hu q
end Ehrhart.BergmanJetJointHolomorphicPhase
