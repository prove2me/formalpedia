-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.differentiable_complex_normalizedShrinkingConvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/3e6aa896-facb-4222-a5cb-c4a4a641d29f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_differentiable_complex_of_weak_barPartial_convolution

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultRegularity
theorem _root_.solution
    {n : ℕ} {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0)) (k : ℕ) :
    Differentiable ℂ
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (TorusCharacters.LogSpace n))
       ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
         (volume : Measure (TorusCharacters.LogSpace n))] g) := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hhol := differentiable_complex_of_weak_barPartial_convolution
    hg hκ hκcompact hweak
  rw [complex_convolution_flip] at hhol
  exact hhol
end Ehrhart.DolbeaultRegularity
