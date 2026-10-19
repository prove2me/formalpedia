-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.hasCompactSupport_sourceAngularDerivativeLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/8e093c5f-0aae-4728-be35-65748931efd6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_hasCompactSupport_angularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_coverAngularSmoothPartition_apply

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
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    HasCompactSupport (sourceAngularDerivativeLift f v) := by
  let w : Space n :=
    ((logarithmicCoordinatesEquiv n).symm v).2
  let κ : Space n → ℝ :=
    fun t => (fderiv ℝ (angularSmoothPartition (n := n)) t) w
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let A : Set (Space n × Space n) :=
    Kr ×ˢ tsupport κ
  let K : Set (TorusCharacters.LogSpace n) :=
    logarithmicCoordinatesEquiv n '' A
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hκ : HasCompactSupport κ :=
    hasCompactSupport_angularSmoothPartition.fderiv_apply ℝ w
  have hA : IsCompact A := hKr.prod hκ
  have hK : IsCompact K :=
    hA.image (logarithmicCoordinatesEquiv n).continuous
  apply HasCompactSupport.intro hK
  intro z hz
  by_contra hnonzero
  have hangular :
      κ ((logarithmicCoordinatesEquiv n).symm z).2 ≠ 0 := by
    intro hzero
    apply hnonzero
    unfold sourceAngularDerivativeLift
    rw [fderiv_coverAngularSmoothPartition_apply]
    change (κ ((logarithmicCoordinatesEquiv n).symm z).2 : ℂ) *
      f (complexTorusCoverProjection n z) = 0
    rw [hzero]
    simp
  have htest : f (complexTorusCoverProjection n z) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [sourceAngularDerivativeLift, hzero]
  apply hz
  refine ⟨(logarithmicCoordinatesEquiv n).symm z, ?_,
    (logarithmicCoordinatesEquiv n).apply_symm_apply z⟩
  refine ⟨?_, subset_closure hangular⟩
  refine ⟨complexTorusCoverProjection n z,
    subset_closure htest, ?_⟩
  rfl
end Ehrhart.MatrixTorusBochnerIdentity
