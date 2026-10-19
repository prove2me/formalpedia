-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.realTorusCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/d7db923c-9816-49e9-8038-453e3d462ffc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_integer_angularFundamentalBoxes_cover
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_realTorusCoverLift_ae_eq_fundamental

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
theorem _root_.solution {n : ℕ}
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g) :
    realTorusCoverLift f =ᵐ[
      (volume : Measure (Space n × Space n))]
      realTorusCoverLift g := by
  have hc :=
    (ae_eq_restrict_iUnion_iff
      (μ := (volume : Measure (Space n × Space n)))
      (fun q : Fin n → ℤ =>
        (Set.univ : Set (Space n)) ×ˢ
          angularFundamentalBox (fun i => (q i : ℝ)))
      (realTorusCoverLift f) (realTorusCoverLift g)).mpr
        (fun q => realTorusCoverLift_ae_eq_fundamental h q)
  simpa [integer_angularFundamentalBoxes_cover] using hc
end Ehrhart.WeightedTorusGraphWeakBridge
