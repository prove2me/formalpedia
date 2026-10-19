-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicPhase.momentJointTailSup_phase_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/00cb57a5-12f5-44d7-ba76-f1aa4e6f2a19

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhase_momentPositiveJointGeodesic_phase_invariant

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
    momentJointTailSup K F htransport p r
        (sourceJointPhaseHomeomorph u hu q) =
      momentJointTailSup K F htransport p r q := by
  unfold momentJointTailSup
  have hfun :
      (fun j : ℕ => momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j)
          (sourceJointPhaseHomeomorph u hu q)) =
      (fun j : ℕ => momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j) q) := by
    funext j
    exact momentPositiveJointGeodesic_phase_invariant
      K F htransport p _ u hu q
  rw [hfun]
end Ehrhart.BergmanJetJointHolomorphicPhase
