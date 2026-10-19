-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/c278dee9-0d9f-4df4-8c90-9eebdd6503c9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_differentiable_complex_normalizedShrinkingConvolution
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_contDiff_normalizedProductRadialKernel
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_hasCompactSupport_normalizedProductRadialKernel
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialHolomorphicMollification_eq_of_differentiable
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexReal_compactKernel_convolution_commute

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
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0))
    (m : ℕ) (z : TorusCharacters.LogSpace n) :
    (((complexShrinkingBump (n := n) m).normed
        (volume : Measure (TorusCharacters.LogSpace n)))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] g) z =
      (((complexShrinkingBump (n := n) m).normed
          (volume : Measure (TorusCharacters.LogSpace n)))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            productRadialHolomorphicMollification g) z := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) m).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  let η : TorusCharacters.LogSpace n → ℝ :=
    normalizedProductRadialKernel
  have hκcont : Continuous κ :=
    (complexShrinkingBump (n := n) m).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) m).hasCompactSupport_normed
  have hηcont : Continuous η :=
    (contDiff_normalizedProductRadialKernel n).continuous
  have hηcompact : HasCompactSupport η :=
    hasCompactSupport_normalizedProductRadialKernel n
  have hhol : Differentiable ℂ
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] g) := by
    exact differentiable_complex_normalizedShrinkingConvolution
      hg hweak m
  have hfix :
      (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z =
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g) z := by
    simpa only [η, productRadialHolomorphicMollification] using
      congrFun
        (productRadialHolomorphicMollification_eq_of_differentiable hhol) z
  have hcomm := complexReal_compactKernel_convolution_commute
    (κ := κ) (η := η) hg
    hκcont hκcompact hηcont hηcompact z
  have hcomm' :
      (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z := by
    simpa only [complex_convolution_flip] using hcomm
  change
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g) z =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
          productRadialHolomorphicMollification g) z
  calc
    _ = (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z :=
      hfix.symm
    _ = (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z :=
      hcomm'
    _ = _ := rfl
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
