-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.weightedTorus_complexCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/a27d9b9c-16c3-44a7-972e-7d422e250bed

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedTorus_ae_eq_unweighted
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_complexTorusCoverLift_ae_eq

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
theorem _root_.solution {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ] g) :
    complexTorusCoverLift f =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))]
      complexTorusCoverLift g :=
  complexTorusCoverLift_ae_eq (weightedTorus_ae_eq_unweighted hφ h)
end Ehrhart.WeightedTorusGraphWeakBridge
