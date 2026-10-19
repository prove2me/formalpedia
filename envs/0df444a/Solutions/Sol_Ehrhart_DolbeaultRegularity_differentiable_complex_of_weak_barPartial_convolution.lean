-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.differentiable_complex_of_weak_barPartial_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/b733697c-4662-47b9-9cf7-563c6fe93c45

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_differentiableAt_complex_of_barPartialCoordinate_eq_zero
import Theorems.Thm_Ehrhart_DolbeaultRegularity_weak_barPartial_convolution_barPartial_eq_zero

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
theorem _root_.solution {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0)) :
    Differentiable ℂ
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) := by
  intro x
  apply differentiableAt_complex_of_barPartialCoordinate_eq_zero
  · exact (hκcompact.hasFDerivAt_convolution_right
      complexRealMultiplication hg hκ x).differentiableAt
  · intro j
    exact weak_barPartial_convolution_barPartial_eq_zero
      hg hκ hκcompact hweak x j
end Ehrhart.DolbeaultRegularity
