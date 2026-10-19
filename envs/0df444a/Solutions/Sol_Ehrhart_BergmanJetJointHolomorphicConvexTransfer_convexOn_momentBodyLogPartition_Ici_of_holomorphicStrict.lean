-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/8081c20f-e4fb-4fe4-af1f-460a36fd9cf9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_momentBodyLogPartition_le_canonicalScale_mul_of_pos
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_convexOn_momentBodyLogPartition_Ioi_of_holomorphicStrict

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicConvexTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetJointHolomorphicConvexTransfer
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    (hstrict : ∀ k : ℕ,
      ConvexOn ℝ (Set.Ioi 0)
        (sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K)
              p (ε k) k))) :
    ConvexOn ℝ (Set.Ici 0)
      (momentBodyLogPartition K p) := by
  apply convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
    (momentBodyLogPartition K p)
    (BodyScale.canonicalScale K)
    (momentBodyLogPartition_zero K p)
    (convexOn_momentBodyLogPartition_Ioi_of_holomorphicStrict
      K p ε hε hε₀ hε₁ hstrict)
  intro t ht
  exact momentBodyLogPartition_le_canonicalScale_mul_of_pos
    K p ht
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
