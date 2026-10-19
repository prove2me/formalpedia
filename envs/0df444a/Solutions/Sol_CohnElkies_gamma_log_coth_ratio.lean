-- Prove2me | solution 1 for CohnElkies.gamma_log_coth_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/326ed856-74e0-4ada-a365-55416269a171

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_gamma_half_add_imaginary_sq
import Theorems.Thm_CohnElkies_norm_gamma_imaginary_sq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ} (hx : x ≠ 0) :
    Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ -
        Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hden : x * Real.sinh (Real.pi * x) ≠ 0 :=
    mul_ne_zero hx hsinh
  have hcosh : Real.cosh (Real.pi * x) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have himaginary :
      2 * Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ =
        Real.log Real.pi -
          Real.log (x * Real.sinh (Real.pi * x)) := by
    calc
      2 * Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ =
          Real.log (‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ = Real.log (Real.pi / (x * Real.sinh (Real.pi * x))) := by
        rw [norm_gamma_imaginary_sq hx]
      _ = Real.log Real.pi -
          Real.log (x * Real.sinh (Real.pi * x)) :=
        Real.log_div Real.pi_ne_zero hden
  have hhalf :
      2 * Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
        Real.log Real.pi - Real.log (Real.cosh (Real.pi * x)) := by
    calc
      2 * Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
          Real.log
            (‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ = Real.log (Real.pi / Real.cosh (Real.pi * x)) := by
        rw [norm_gamma_half_add_imaginary_sq]
      _ = Real.log Real.pi - Real.log (Real.cosh (Real.pi * x)) :=
        Real.log_div Real.pi_ne_zero hcosh
  have hcoth :
      lowerCoth (Real.pi * |x|) / |x| =
        Real.cosh (Real.pi * x) /
          (x * Real.sinh (Real.pi * x)) := by
    rcases lt_or_gt_of_ne hx with hnegative | hpositive
    · rw [abs_of_neg hnegative]
      unfold lowerCoth
      have harg : Real.pi * -x = -(Real.pi * x) := by ring
      rw [harg, Real.cosh_neg, Real.sinh_neg]
      field_simp [hx, hsinh]
    · rw [abs_of_pos hpositive]
      unfold lowerCoth
      field_simp [hx, hsinh]
  have hlogcoth :
      Real.log (Real.cosh (Real.pi * x)) -
          Real.log (x * Real.sinh (Real.pi * x)) =
        Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
    rw [hcoth, Real.log_div hcosh hden]
  calc
    Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ -
        Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
      (1 / 2 : ℝ) *
        ((Real.log Real.pi -
            Real.log (x * Real.sinh (Real.pi * x))) -
          (Real.log Real.pi - Real.log (Real.cosh (Real.pi * x)))) := by
        linarith
    _ = (1 / 2 : ℝ) *
          (Real.log (Real.cosh (Real.pi * x)) -
            Real.log (x * Real.sinh (Real.pi * x))) := by
        ring
    _ = (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
        rw [hlogcoth]
end CohnElkies
