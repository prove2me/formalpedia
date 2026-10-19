-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.smoothConvexPotential_upper_of_support_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/44b1767a-a54c-4342-9146-e9f59d609006

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (q : LogTorus n) :
    a q ≤ smoothConvexPotential K q.1 + (C + 1) := by
  have hb := (abs_le.mp
    (smoothConvexPotential_bounded K q.1)).1
  linarith [hupper q]
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
