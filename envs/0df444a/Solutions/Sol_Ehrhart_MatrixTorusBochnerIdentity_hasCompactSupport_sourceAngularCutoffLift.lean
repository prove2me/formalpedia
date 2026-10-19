-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.hasCompactSupport_sourceAngularCutoffLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/b5505bea-72a9-4f0b-8c76-f9a48ae513bb

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
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (sourceAngularCutoffLift f) := by
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let A : Set (Space n × Space n) :=
    Kr ×ˢ tsupport (angularSmoothPartition (n := n))
  let K : Set (TorusCharacters.LogSpace n) :=
    logarithmicCoordinatesEquiv n '' A
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hA : IsCompact A :=
    hKr.prod hasCompactSupport_angularSmoothPartition
  have hK : IsCompact K :=
    hA.image (logarithmicCoordinatesEquiv n).continuous
  apply HasCompactSupport.intro hK
  intro z hz
  by_contra hnonzero
  have hangular :
      angularSmoothPartition
        ((logarithmicCoordinatesEquiv n).symm z).2 ≠ 0 := by
    intro hzero
    apply hnonzero
    change
      (angularSmoothPartition
        ((logarithmicCoordinatesEquiv n).symm z).2 : ℂ) *
        f (complexTorusCoverProjection n z) = 0
    rw [hzero]
    simp
  have htest : f (complexTorusCoverProjection n z) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [sourceAngularCutoffLift, hzero]
  apply hz
  refine ⟨(logarithmicCoordinatesEquiv n).symm z, ?_,
    (logarithmicCoordinatesEquiv n).apply_symm_apply z⟩
  refine ⟨?_, subset_closure hangular⟩
  refine ⟨complexTorusCoverProjection n z,
    subset_closure htest, ?_⟩
  rfl
end Ehrhart.MatrixTorusBochnerIdentity
