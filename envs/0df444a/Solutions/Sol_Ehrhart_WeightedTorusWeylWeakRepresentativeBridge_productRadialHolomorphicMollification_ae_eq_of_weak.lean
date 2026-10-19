-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.productRadialHolomorphicMollification_ae_eq_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/a038aa67-2ec3-4f74-b907-7f21ff8ffc71

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexShrinkingBump_rOut_tendsto
import Theorems.Thm_Ehrhart_DolbeaultRegularity_ae_tendsto_normalized_holomorphic_mollifications
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_differentiable_productRadialHolomorphicMollification
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_normalizedShrinkingConvolution_eq_radialRepresentativeConvolution

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedBrascampSaturation DolbeaultRegularity ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusWeylRepresentativeBridge
open WeightedTorusWeylRadialIntegrationBridge
namespace Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0)) :
    productRadialHolomorphicMollification g =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))] g := by
  have hhol := differentiable_productRadialHolomorphicMollification
    hg hweak
  filter_upwards [ae_tendsto_normalized_holomorphic_mollifications hg]
    with z hz
  have hradial : Tendsto
      (fun m : ℕ =>
        (((complexShrinkingBump (n := n) m).normed
            (volume : Measure (TorusCharacters.LogSpace n)))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            (volume : Measure (TorusCharacters.LogSpace n))]
              productRadialHolomorphicMollification g) z)
      atTop (nhds (productRadialHolomorphicMollification g z)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (complexShrinkingBump_rOut_tendsto (n := n)) hhol.continuous z
  have hto_g : Tendsto
      (fun m : ℕ =>
        (((complexShrinkingBump (n := n) m).normed
            (volume : Measure (TorusCharacters.LogSpace n)))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            (volume : Measure (TorusCharacters.LogSpace n))]
              productRadialHolomorphicMollification g) z)
      atTop (nhds (g z)) := by
    exact hz.congr' (Filter.Eventually.of_forall fun m =>
      normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
        hg hweak m z)
  exact tendsto_nhds_unique hradial hto_g
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
