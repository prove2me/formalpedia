-- Prove2me | solution 1 for Ehrhart.TorusDeckCompactSupport.hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/afa6067a-1873-4314-8731-8f88013d1e9b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_complexDeckPeriodization_periodic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckCompactSupport
open Set Function Filter MeasureTheory Matrix
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open MatrixTorusBochnerIdentity TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckCompactSupport
theorem _root_.solution
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ) :
    HasCompactSupport
      (torusScalarRepresentative (complexDeckPeriodization ψ)) := by
  classical
  let K : Set (WeightedTorusHilbert.LogTorus n) :=
    complexTorusCoverProjection n '' tsupport ψ
  have hK : IsCompact K :=
    hψcompact.image (continuous_complexTorusCoverProjection n)
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hnonzero
  obtain ⟨z, hz⟩ :=
    (complexTorusCoverProjection_isOpenQuotientMap n).surjective p
  have hvalue : complexDeckPeriodization ψ z ≠ 0 := by
    intro hzero
    apply hnonzero
    have hrep := congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (complexDeckPeriodization ψ)
        (fun q => complexDeckPeriodization_periodic ψ q)) z
    change
      torusScalarRepresentative (complexDeckPeriodization ψ)
        (complexTorusCoverProjection n z) =
        complexDeckPeriodization ψ z at hrep
    rw [hz, hzero] at hrep
    exact hrep
  have hexists :
      ∃ q : Fin n → ℤ,
        ψ (z + TorusCharacters.imaginaryShift q) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hvalue
    simp [complexDeckPeriodization, hnone]
  obtain ⟨q, hq⟩ := hexists
  apply hp
  refine ⟨z + TorusCharacters.imaginaryShift q,
    subset_closure ((mem_support).mpr hq), ?_⟩
  rw [complexTorusCoverProjection_imaginaryShift, hz]
end Ehrhart.TorusDeckCompactSupport
