-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_momentBodyLogPartition_Ioi_of_holomorphicStrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/45335f30-4a09-4bf6-a324-2d91c5e9e7b4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_momentBodyLogPartition_eq_sourceLogPartition_add_log_volume
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_convexOn_momentWeakHolomorphicEnvelopeLogPartition_Ioi_of_strict

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
    ConvexOn ℝ (Set.Ioi 0)
      (momentBodyLogPartition K p) := by
  have hweak :=
    convexOn_momentWeakHolomorphicEnvelopeLogPartition_Ioi_of_strict
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
        p ε hε hε₀ hε₁ hstrict
  have hconstant :
      ConvexOn ℝ (Set.Ioi (0 : ℝ))
        (fun _ : ℝ => Real.log (normalizedVolume K.carrier)) :=
    convexOn_const
      (Real.log (normalizedVolume K.carrier))
      (convex_Ioi (0 : ℝ))
  have hadd := hweak.add hconstant
  have heq :
      momentBodyLogPartition K p =
        (fun t : ℝ =>
          sourceLogPartition
            (fun (u : ℝ) (q : LogTorus n) =>
              momentTorusEnvelopeTimeSlice
                K (momentBodyOptimizer K)
                  (momentBodyOptimizer_transport K)
                  p q u) t +
            Real.log (normalizedVolume K.carrier)) := by
    funext t
    rw [momentBodyLogPartition_eq_sourceLogPartition_add_log_volume]
    rfl
  rw [heq]
  exact hadd
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
