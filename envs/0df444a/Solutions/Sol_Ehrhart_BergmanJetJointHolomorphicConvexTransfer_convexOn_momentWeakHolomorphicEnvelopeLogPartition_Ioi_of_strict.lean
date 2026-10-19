-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_momentWeakHolomorphicEnvelopeLogPartition_Ioi_of_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/05201e87-8da8-412e-8746-e7f5862618f0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_tendsto_momentWeakHolomorphicStrictJointLogPartition

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
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    (hstrict : ∀ k : ℕ,
      ConvexOn ℝ (Set.Ioi 0)
        (sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k))) :
    ConvexOn ℝ (Set.Ioi 0)
      (sourceLogPartition
        (fun (t : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q t)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 < x at hx
  change 0 < y at hy
  have hm : 0 < a * x + b * y := by
    rcases ha.eq_or_lt with hazero | hapos
    · have ha0 : a = 0 := hazero.symm
      have hb1 : b = 1 := by linarith
      simp [ha0, hb1, hy]
    · nlinarith [mul_pos hapos hx, mul_nonneg hb hy.le]
  have hmid :=
    tendsto_momentWeakHolomorphicStrictJointLogPartition
      K F htransport p ε hε hε₀ hε₁ hm
  have hleft :=
    tendsto_momentWeakHolomorphicStrictJointLogPartition
      K F htransport p ε hε hε₀ hε₁ hx
  have hright :=
    tendsto_momentWeakHolomorphicStrictJointLogPartition
      K F htransport p ε hε hε₀ hε₁ hy
  change
    sourceLogPartition
      (fun (t : ℝ) (q : LogTorus n) =>
        momentTorusEnvelopeTimeSlice K F htransport p q t)
      (a * x + b * y) ≤
      a * sourceLogPartition
        (fun (t : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q t) x +
      b * sourceLogPartition
        (fun (t : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q t) y
  apply le_of_tendsto_of_tendsto hmid
    ((hleft.const_mul a).add (hright.const_mul b))
  exact Filter.Eventually.of_forall fun k => by
    simpa [smul_eq_mul] using
      (hstrict k).2 hx hy ha hb hab
end Ehrhart.BergmanJetJointHolomorphicConvexTransfer
