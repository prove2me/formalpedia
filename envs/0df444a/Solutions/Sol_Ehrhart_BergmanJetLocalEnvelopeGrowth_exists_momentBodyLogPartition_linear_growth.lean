-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.exists_momentBodyLogPartition_linear_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/85464a48-a508-40cf-a9ef-19ca04b7a2b1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_momentBodyLogPartition_le_linear

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalEnvelopeGrowth
open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetLocalEnvelopeGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      momentBodyLogPartition K (0 : LogSpace n) t ≤
        (n : ℝ) * t + C := by
  refine ⟨max (momentBodyLocalPartitionGrowthConstant K 1) 0, ?_⟩
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · rw [momentBodyLogPartition_zero]
    simp only [mul_zero, zero_add]
    exact le_max_right _ _
  · calc
      momentBodyLogPartition K (0 : LogSpace n) t ≤
        (n : ℝ) * t + momentBodyLocalPartitionGrowthConstant K 1 :=
          momentBodyLogPartition_le_linear K 1 t (by norm_num) ht
      _ ≤ (n : ℝ) * t +
        max (momentBodyLocalPartitionGrowthConstant K 1) 0 := by
          gcongr
          exact le_max_left _ _
end Ehrhart.BergmanJetLocalEnvelopeGrowth
