-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.weightedTorus_representative_ae_of_complexCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1b3e48e1-0b3c-472b-8c88-27f8b38e5b6b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_unweightedTorus_ae_eq_weighted
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_unweightedTorus_representative_ae_of_complexCover

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ComplexSaturatedKillingFieldBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility
namespace Ehrhart.ComplexSaturatedKillingFieldBridge
theorem _root_.solution
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hcover : F =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))]
        complexTorusCoverLift f) :
    (fun z : WeightedTorusHilbert.LogTorus n => f z) =ᵐ[
      weightedTorusMeasure k φ]
        (fun z => coverRepresentative F z.1 z.2) := by
  exact unweightedTorus_ae_eq_weighted hφ
    (unweightedTorus_representative_ae_of_complexCover hcover)
end Ehrhart.ComplexSaturatedKillingFieldBridge
