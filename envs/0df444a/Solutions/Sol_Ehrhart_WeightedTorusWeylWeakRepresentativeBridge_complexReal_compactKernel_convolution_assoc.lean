-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexReal_compactKernel_convolution_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/02cf520b-0b65-4b56-8848-352c58e6224b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_locallyIntegrable_norm
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_hasCompactSupport_normConvolution
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_continuous_normConvolution

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
theorem _root_.solution {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκcont : Continuous κ) (hκcompact : HasCompactSupport κ)
    (hηcont : Continuous η) (hηcompact : HasCompactSupport η)
    (z : TorusCharacters.LogSpace n) :
    ((g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] η) z =
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] η)) z := by
  have hκint : Integrable κ
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    hκcont.integrable_of_hasCompactSupport hκcompact
  have hηint : Integrable η
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    hηcont.integrable_of_hasCompactSupport hηcompact
  refine MeasureTheory.convolution_assoc
    complexRealMultiplication complexRealMultiplication
    complexRealMultiplication (ContinuousLinearMap.mul ℝ ℝ)
    ?_ hg.aestronglyMeasurable hκcont.aestronglyMeasurable
    hηcont.aestronglyMeasurable ?_ ?_ ?_
  · intro w a b
    change (b : ℂ) * ((a : ℂ) * w) =
      ((a * b : ℝ) : ℂ) * w
    push_cast
    ring
  · exact Filter.Eventually.of_forall
      (hκcompact.convolutionExists_right
        complexRealMultiplication hg hκcont)
  · exact hκint.norm.ae_convolution_exists
      (ContinuousLinearMap.mul ℝ ℝ) hηint.norm
  · exact (complexCover_hasCompactSupport_normConvolution
      hκcompact hηcompact).convolutionExists_right
        (ContinuousLinearMap.mul ℝ ℝ)
        (complexCover_locallyIntegrable_norm hg)
        (complexCover_continuous_normConvolution
          hκcont hκcompact hηcont hηcompact) z
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
