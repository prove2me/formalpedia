-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.measurable_momentBodyEnvelopePositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/be4ebdbf-51cc-4760-a63b-e1fdf3d2344d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_measurable_momentBodyTorusWeight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Measurable (momentBodyEnvelopePositiveSecant K p t) := by
  unfold momentBodyEnvelopePositiveSecant
  exact ((measurable_momentBodyTorusWeight K p t).sub
    (measurable_momentBodyTorusWeight K p 0)).div_const t
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
