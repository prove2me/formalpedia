-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.measurable_momentBodyEnvelopeRelativeDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/581e5b11-1601-4283-92ed-674b5e11f554

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
open Ehrhart.BergmanJetBodyExponentialSecantBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBodyExponentialSecantBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Measurable (momentBodyEnvelopeRelativeDensity K p t) := by
  unfold momentBodyEnvelopeRelativeDensity
  exact Real.continuous_exp.measurable.comp
    ((measurable_momentBodyTorusWeight K p t).sub
      (measurable_momentBodyTorusWeight K p 0)).neg
end Ehrhart.BergmanJetBodyExponentialSecantBridge
