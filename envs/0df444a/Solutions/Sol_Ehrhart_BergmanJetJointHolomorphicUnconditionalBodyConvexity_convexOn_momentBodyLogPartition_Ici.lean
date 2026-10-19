-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicUnconditionalBodyConvexity.convexOn_momentBodyLogPartition_Ici
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/afbea61d-4237-4cff-9337-0ec121013944

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicUnconditionalBodyConvexity
open Set Function Filter
open TorusCharacters BergmanJetPartitionEndpoint BergmanJetHolomorphicPhysicalLogConvexity
open BergmanJetJointHolomorphicConvexTransfer
open scoped Topology
namespace Ehrhart.BergmanJetJointHolomorphicUnconditionalBodyConvexity
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    ConvexOn ℝ (Set.Ici 0)
      (momentBodyLogPartition K p) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  have hεle (k : ℕ) : ε k ≤ 1 := by
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hnonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    dsimp [ε]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  apply convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
    K p ε hε (fun k => (hεpos k).le) hεle
  intro k
  exact convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K)
    p (ε k) (hεpos k) (hεle k) k
end Ehrhart.BergmanJetJointHolomorphicUnconditionalBodyConvexity
