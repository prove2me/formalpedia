-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexReal_compactKernel_convolution_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/5a974b14-7c20-441c-b16e-82260919bce7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexReal_compactKernel_convolution_assoc
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_real_convolution_comm

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
      ((g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] η)
      ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) z := by
  calc
    _ = (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] η)) z :=
      complexReal_compactKernel_convolution_assoc hg
        hκcont hκcompact hηcont hηcompact z
    _ = (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (η ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] κ)) z := by
      rw [complexCover_real_convolution_comm κ η]
    _ = _ := (complexReal_compactKernel_convolution_assoc hg
      hηcont hηcompact hκcont hκcompact z).symm
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
