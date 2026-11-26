-- Prove2me | solution 1 for Aux_w_53_hermite.x_mul_h1D_eq
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:19.087541+00:00
-- url     : https://prove2.me/submissions/cddb1f60-3a9d-4979-9ed8-5c26ac5b7d0e

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
import Theorems.Thm_Aux_w_53_hermite_derivative_hermite
section
set_option autoImplicit false

namespace Aux_w_53_hermite

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density, Orthonormal Hermite Functions, and `sgn` Coefficients -/























lemma Hpoly_succ (j : ℕ) (x : ℝ) :
    Hpoly (j + 1) x = x * Hpoly j x - (j : ℝ) * (if j = 0 then 0 else Hpoly (j - 1) x) := by
  cases j with
  | zero => simp [Hpoly, Polynomial.hermite_zero]
  | succ k =>
    have hderiv : Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite (k + 1))) =
        ((k + 1 : ℕ) : ℝ) * Polynomial.aeval x (Polynomial.hermite k) := by
      rw [derivative_hermite k, map_mul]
      simp
    simp only [Hpoly, Polynomial.hermite_succ (k + 1), map_sub, map_mul, Polynomial.aeval_X]
    rw [hderiv]
    simp





























































/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/





























end Aux_w_53_hermite


end
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal
theorem solution (j : ℕ) (x : ℝ) :
    x * Aux_w_53_hermite.h1D j x = Real.sqrt (j + 1 : ℝ) * Aux_w_53_hermite.h1D (j + 1) x +
      (if j = 0 then 0 else Real.sqrt (j : ℝ) * Aux_w_53_hermite.h1D (j - 1) x) := by
  have hsqrt1 : (0 : ℝ) < j + 1 := by positivity
  have hfac1 : Real.sqrt ((j + 1).factorial : ℝ) =
      Real.sqrt (j + 1 : ℝ) * Real.sqrt (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul hsqrt1.le]
  have h1 : Real.sqrt (j + 1 : ℝ) * Aux_w_53_hermite.h1D (j + 1) x =
      (Real.sqrt (j.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (j + 1) x := by
    rw [Aux_w_53_hermite.h1D, hfac1, mul_inv]
    have hne : Real.sqrt (j + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hsqrt1
    calc Real.sqrt (j + 1 : ℝ) *
          ((Real.sqrt (j + 1 : ℝ))⁻¹ * (Real.sqrt (j.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (j + 1) x)
        = (Real.sqrt (j + 1 : ℝ) * (Real.sqrt (j + 1 : ℝ))⁻¹) *
            ((Real.sqrt (j.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (j + 1) x) := by ring
      _ = (Real.sqrt (j.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (j + 1) x := by
            rw [mul_inv_cancel₀ hne, one_mul]
  rw [h1, Aux_w_53_hermite.Hpoly_succ j x]
  cases j with
  | zero => simp [Aux_w_53_hermite.h1D]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hfac2 : Real.sqrt ((k + 1).factorial : ℝ) =
        Real.sqrt (k + 1 : ℝ) * Real.sqrt (k.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul hk.le]
    have hsq : Real.sqrt (k + 1 : ℝ) * Real.sqrt (k + 1 : ℝ) = (k + 1 : ℝ) :=
      Real.mul_self_sqrt hk.le
    rw [Aux_w_53_hermite.h1D, Aux_w_53_hermite.h1D, hfac2, mul_inv]
    have hne : Real.sqrt (k + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hk
    have hfac_ne : Real.sqrt (k.factorial : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    field_simp
    push_cast
    rw [mul_right_comm (Real.sqrt ((k : ℝ) + 1)) (Aux_w_53_hermite.Hpoly k x) (Real.sqrt ((k : ℝ) + 1)), hsq]
    ring
