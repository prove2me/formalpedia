-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.exp_neg_dimension_mul_le_momentBodyNormalizedPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/9480a83e-d00e-480a-96e2-ec44e3fbe254

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_momentBodyNormalizedPartition_pos
import Theorems.Thm_Ehrhart_BergmanJetBodyLogPartitionSharpGrowth_momentBodyLogPartition_le_dimension_mul

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
    {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-((n : ℝ) * t)) ≤
      momentBodyNormalizedPartition K (0 : LogSpace n) t := by
  have hgrowth := momentBodyLogPartition_le_dimension_mul K ht
  have hpos := momentBodyNormalizedPartition_pos
    K (0 : LogSpace n) t
  have hlog :
      -((n : ℝ) * t) ≤
        Real.log
          (momentBodyNormalizedPartition K
            (0 : LogSpace n) t) := by
    unfold momentBodyLogPartition at hgrowth
    linarith
  calc
    Real.exp (-((n : ℝ) * t)) ≤
      Real.exp
        (Real.log (momentBodyNormalizedPartition
          K (0 : LogSpace n) t)) := Real.exp_le_exp.mpr hlog
    _ = momentBodyNormalizedPartition
          K (0 : LogSpace n) t := Real.exp_log hpos
end Ehrhart.BergmanJetBodyExponentialSecantBridge
