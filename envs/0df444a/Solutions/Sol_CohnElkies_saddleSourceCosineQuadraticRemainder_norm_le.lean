-- Prove2me | solution 1 for CohnElkies.saddleSourceCosineQuadraticRemainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/fcdd13d3-7544-442a-8cec-9d31d3cc8c4b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_quadratic_remainder_norm_le
import Theorems.Thm_CohnElkies_saddleSourceCosineQuadraticRemainder_eq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (a u T : ℝ) :
    ‖saddleSourceCosineQuadraticRemainder a u T‖ ≤
      Real.cosh (u * a) * |a * T| ^ 3 / 6 := by
  rw [saddleSourceCosineQuadraticRemainder_eq]
  have hfirst := upperImaginaryExp_quadratic_remainder_norm_le
    (a * T)
  have hsecond := upperImaginaryExp_quadratic_remainder_norm_le
    (-(a * T))
  have hwfirst : 0 ≤ Real.exp (-(u * a)) / 2 := by
    positivity
  have hwsecond : 0 ≤ Real.exp (u * a) / 2 := by
    positivity
  calc
    ‖((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (a * T) - 1 -
            Complex.I * ((a * T : ℝ) : ℂ) +
              (((a * T) ^ 2 / 2 : ℝ) : ℂ)) +
        ((Real.exp (u * a) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (-(a * T)) - 1 -
            Complex.I * ((-(a * T) : ℝ) : ℂ) +
              (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      ‖((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (a * T) - 1 -
            Complex.I * ((a * T : ℝ) : ℂ) +
              (((a * T) ^ 2 / 2 : ℝ) : ℂ))‖ +
        ‖((Real.exp (u * a) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (-(a * T)) - 1 -
            Complex.I * ((-(a * T) : ℝ) : ℂ) +
              (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ))‖ :=
        norm_add_le _ _
    _ = (Real.exp (-(u * a)) / 2) *
          ‖upperImaginaryExp (a * T) - 1 -
            Complex.I * ((a * T : ℝ) : ℂ) +
              (((a * T) ^ 2 / 2 : ℝ) : ℂ)‖ +
        (Real.exp (u * a) / 2) *
          ‖upperImaginaryExp (-(a * T)) - 1 -
            Complex.I * ((-(a * T) : ℝ) : ℂ) +
              (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ)‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hwfirst, abs_of_nonneg hwsecond]
    _ ≤ (Real.exp (-(u * a)) / 2) *
          (|a * T| ^ 3 / 6) +
        (Real.exp (u * a) / 2) *
          (|a * T| ^ 3 / 6) := by
        have hsecond' :
            ‖upperImaginaryExp (-(a * T)) - 1 -
              Complex.I * ((-(a * T) : ℝ) : ℂ) +
                (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
              |a * T| ^ 3 / 6 := by
          simpa [abs_neg] using! hsecond
        gcongr
    _ = Real.cosh (u * a) * |a * T| ^ 3 / 6 := by
      rw [Real.cosh_eq]
      ring
end CohnElkies
