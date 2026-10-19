-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.hasCompactSupport_partitionedRealCoverIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/86ba2109-8bfb-4d11-8643-a5f53960f994

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_hasCompactSupport_angularSmoothPartition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} {φ : Space n → ℝ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (partitionedRealCoverIntegrand φ f) := by
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let K : Set (Space n × Space n) :=
    Kr ×ˢ tsupport (angularSmoothPartition (n := n))
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hK : IsCompact K :=
    hKr.prod hasCompactSupport_angularSmoothPartition
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hnonzero
  have hangular : angularSmoothPartition p.2 ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [partitionedRealCoverIntegrand, hzero]
  have htest : f (p.1, angularCoverProjection n p.2) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [partitionedRealCoverIntegrand, hzero]
  apply hp
  exact ⟨⟨(p.1, angularCoverProjection n p.2),
    subset_closure htest, rfl⟩, subset_closure hangular⟩
end Ehrhart.MatrixTorusBochnerBridge
