-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.one_sub_momentBodyNormalizedPartition_le_dimension_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/c4de56c3-dc9c-4f69-882d-f2dcfce6a163

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_exp_neg_dimension_mul_le_momentBodyNormalizedPartition

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
    1 - momentBodyNormalizedPartition
      K (0 : LogSpace n) t ≤ (n : ℝ) * t := by
  have hpart :=
    exp_neg_dimension_mul_le_momentBodyNormalizedPartition K ht
  have hexp := Real.add_one_le_exp (-((n : ℝ) * t))
  linarith
end Ehrhart.BergmanJetBodyExponentialSecantBridge
