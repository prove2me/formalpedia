-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhase.momentPositiveJointGeodesic_phase_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/6010778f-25b6-4f17-a2fa-7406d9d77109

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonic_sourceJointPhaseHomeomorph_spatial
import Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonic_jointLogTime_sourceJointPhaseHomeomorph

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
    (p : LogSpace n) (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k
        (sourceJointPhaseHomeomorph u hu q) =
      momentPositiveJointGeodesic K F htransport p k q := by
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
    momentPositiveJointGeodesic_eq_momentJetGeodesic,
    sourceJointPhaseHomeomorph_spatial,
    jointLogTime_sourceJointPhaseHomeomorph]
end Ehrhart.BergmanJetJointHolomorphicPhase
