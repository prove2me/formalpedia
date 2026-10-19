-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.hasCompactSupport_derivativePartitionedRealCoverIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/3813ac0d-9ed1-4d5d-bf70-d3659e0190e7

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
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} {φ : Space n → ℝ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f)
    (v : Space n) :
    HasCompactSupport
      (derivativePartitionedRealCoverIntegrand φ f v) := by
  let κ : Space n → ℝ :=
    fun t => (fderiv ℝ (angularSmoothPartition (n := n)) t) v
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let K : Set (Space n × Space n) :=
    Kr ×ˢ tsupport κ
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hκ : HasCompactSupport κ :=
    hasCompactSupport_angularSmoothPartition.fderiv_apply ℝ v
  have hK : IsCompact K := hKr.prod hκ
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hnonzero
  have hangular : κ p.2 ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [derivativePartitionedRealCoverIntegrand, κ, hzero]
  have htest : f (p.1, angularCoverProjection n p.2) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [derivativePartitionedRealCoverIntegrand, hzero]
  apply hp
  exact ⟨⟨(p.1, angularCoverProjection n p.2),
    subset_closure htest, rfl⟩, subset_closure hangular⟩
end Ehrhart.MatrixTorusBochnerIdentity
