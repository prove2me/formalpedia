-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_factorized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/b7331ab0-ac26-499e-a0ae-8fc620bf68d3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_half_integer_gamma_product
import Theorems.Thm_CohnElkies_gamma_imaginary_ne_zero
import Theorems.Thm_CohnElkies_norm_gamma_neg_imaginary
import Theorems.Thm_CohnElkies_norm_halfIntegerGammaFactor
import Theorems.Thm_CohnElkies_halfIntegerGammaFactor_ne_zero

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (Real.log ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖) := by
  have himaginary :
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_imaginary_ne_zero hy)
  have hreflection :
      ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
        ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
    apply (div_eq_one_iff_eq himaginary).mp
    rw [norm_gamma_neg_imaginary, div_self himaginary]
  have hbase :
      Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  have hbasenorm :
      ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hbase
  have hproduct :
      (∏ j ∈ Finset.range k,
        ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun j _ => halfIntegerGammaFactor_ne_zero j y)
  have hproductnorm :
      ‖∏ j ∈ Finset.range k,
        ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hproduct
  have hlogproduct :
      Real.log
        ‖∏ j ∈ Finset.range k,
          ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖ =
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    rw [Complex.norm_prod]
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro j _
      rw [norm_halfIntegerGammaFactor]
    · intro j _
      exact norm_ne_zero_iff.mpr (halfIntegerGammaFactor_ne_zero j y)
  have hcast :
      (((k : ℝ) + 1 / 2 : ℝ) : ℂ) =
        (k : ℂ) + (1 / 2 : ℂ) := by
    push_cast
    rfl
  unfold lowerGammaBoundaryLog
  rw [hcast, half_integer_gamma_product k y, norm_mul,
    Real.log_mul hbasenorm hproductnorm,
    hreflection, hlogproduct]
  ring
end CohnElkies
