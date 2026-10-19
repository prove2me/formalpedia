-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.differentiableAt_complex_of_barPartialCoordinate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/78bed9a7-f0cf-448f-924e-61c919f1314f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexContinuousOfCoordinateCR_restrictScalars

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
    {n : ℕ} {F : TorusCharacters.LogSpace n → ℂ}
    {z : TorusCharacters.LogSpace n}
    (hF : DifferentiableAt ℝ F z)
    (hbar : ∀ j : Fin n, barPartialCoordinate F z j = 0) :
    DifferentiableAt ℂ F z := by
  let D : TorusCharacters.LogSpace n →L[ℝ] ℂ := fderiv ℝ F z
  have hI : ∀ j : Fin n,
      D (Pi.single j Complex.I) =
        Complex.I • D (Pi.single j (1 : ℂ)) := by
    intro j
    have hz := hbar j
    unfold barPartialCoordinate at hz
    have hnum :
        (fderiv ℝ F z) (Pi.single j (1 : ℂ)) +
          Complex.I * (fderiv ℝ F z)
            (Pi.single j Complex.I) = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact h
      · norm_num at h
    change
      (fderiv ℝ F z) (Pi.single j Complex.I) =
        Complex.I * (fderiv ℝ F z) (Pi.single j (1 : ℂ))
    have hsq : Complex.I ^ 2 = (-1 : ℂ) := by
      simp [pow_two, Complex.I_mul_I]
    linear_combination -Complex.I * hnum +
      (fderiv ℝ F z) (Pi.single j Complex.I) * hsq
  apply (differentiableAt_iff_restrictScalars ℝ hF).mpr
  refine ⟨complexContinuousOfCoordinateCR D hI, ?_⟩
  exact complexContinuousOfCoordinateCR_restrictScalars D hI
end Ehrhart.DolbeaultRegularity
