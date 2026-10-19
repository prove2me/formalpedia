-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.weightedSmoothGraphGenerator_compact_barPartial_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/08875949-3622-4933-8472-b958abd826f9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultGraphDistributionBridge_complex_compact_barPartial_green
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedScalarGraphGenerator_complexCoverLift_ae_eq
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedFormGraphGenerator_complexCoverLift_ae_eq

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
    (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ))
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n =>
          torusScalarL2OfRepresentative φ F hF p) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : TorusCharacters.LogSpace n,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n =>
              (torusFunctionBarPartialL2 φ F hD p :
                EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      F z * coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
        apply integral_congr_ae
        filter_upwards
          [weightedScalarGraphGenerator_complexCoverLift_ae_eq
            hφ F hperiod hF] with z hz
        rw [hz]
    _ = -(2 : ℂ) *
      (∫ z : TorusCharacters.LogSpace n,
        barPartialCoordinate F z j * (ψ z : ℂ)
        ∂(volume : Measure (TorusCharacters.LogSpace n))) :=
      complex_compact_barPartial_green hF₁ hψ hψcompact j
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards
        [weightedFormGraphGenerator_complexCoverLift_ae_eq
          hφ F hperiod hD j] with z hz
      rw [hz]
end Ehrhart.WeightedTorusGraphWeakBridge
