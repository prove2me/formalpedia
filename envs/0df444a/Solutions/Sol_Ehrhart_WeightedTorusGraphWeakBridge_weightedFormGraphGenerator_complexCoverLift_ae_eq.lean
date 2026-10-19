-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.weightedFormGraphGenerator_complexCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/3eb05e0d-e7be-40eb-9907-b19dd540d4cd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedTorus_complexCoverLift_ae_eq
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_complexTorusCoverLift_barPartialRepresentative_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.WeightedTorusGraphWeakBridge
theorem _root_.solution
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ))
    (j : Fin n) :
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialL2 φ F hD z :
          EuclideanSpace ℂ (Fin n)) j) =ᵐ[
            (volume : Measure (TorusCharacters.LogSpace n))]
      (fun z => barPartialCoordinate F z j) := by
  have hrow := hD.coeFn_toLp
  have hj :
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialL2 φ F hD z :
          EuclideanSpace ℂ (Fin n)) j) =ᵐ[
            WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialRepresentative F z :
          EuclideanSpace ℂ (Fin n)) j) := by
    filter_upwards [hrow] with z hz
    exact congrFun (congrArg WithLp.ofLp hz) j
  have h := weightedTorus_complexCoverLift_ae_eq hφ hj
  rw [complexTorusCoverLift_barPartialRepresentative_eq F hperiod j] at h
  exact h
end Ehrhart.WeightedTorusGraphWeakBridge
