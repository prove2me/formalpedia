-- Prove2me | solution 1 for Aux_w_53_hermite.hasDerivAt_h1D_mul_phi
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:13.860444+00:00
-- url     : https://prove2.me/submissions/faf72b9b-7d98-4334-b5ce-bbe28538441c

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
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_phi
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
    HasDerivAt (fun y => Aux_w_53_hermite.h1D j y * Aux_w_53_hermite.phi y) (-Real.sqrt (j + 1 : ℝ) * Aux_w_53_hermite.h1D (j + 1) x * Aux_w_53_hermite.phi x) x := by
  cases j with
  | zero =>
    have hfn : (fun y => Aux_w_53_hermite.h1D 0 y * Aux_w_53_hermite.phi y) = Aux_w_53_hermite.phi := by ext y; simp [Aux_w_53_hermite.h1D_zero_fn]
    rw [hfn]
    refine (Aux_w_53_hermite.hasDerivAt_phi x).congr_deriv ?_
    simp [Aux_w_53_hermite.h1D, Aux_w_53_hermite.Hpoly]
  | succ k =>
    have h1 := (Aux_w_53_hermite.hasDerivAt_h1D (k + 1) x).mul (Aux_w_53_hermite.hasDerivAt_phi x)
    refine h1.congr_deriv ?_
    have hrec := Aux_w_53_hermite.Hpoly_succ (k + 1) x
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at hrec
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hfac : (Real.sqrt ((k + 2).factorial : ℝ))⁻¹ =
        (Real.sqrt (k + 2 : ℝ))⁻¹ * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ (k + 1), Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
      rw [show (((k + 1 + 1 : ℕ) : ℝ)) = k + 2 by push_cast; ring, mul_comm]
    have hfac2 : (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ =
        (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ k, Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
      rw [show (((k + 1 : ℕ) : ℝ)) = k + 1 by push_cast; ring, mul_comm]
    have hsq : (k + 1 : ℝ) * (Real.sqrt (k + 1 : ℝ))⁻¹ = Real.sqrt (k + 1 : ℝ) := by
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (Real.sqrt_ne_zero'.mpr hk1), Real.mul_self_sqrt hk1.le]
    have hsqrt_cancel : Real.sqrt (k + 2 : ℝ) * (Real.sqrt (k + 2 : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hk2)
    simp only [Aux_w_53_hermite.h1D_deriv, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, Aux_w_53_hermite.h1D]
    rw [show (k + 1 : ℕ) + 1 = k + 2 from rfl, hrec, hfac]
    push_cast
    calc Real.sqrt (k + 1 : ℝ) * ((Real.sqrt (k.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly k x) * Aux_w_53_hermite.phi x +
          (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (k + 1) x * (-x * Aux_w_53_hermite.phi x)
        = (Real.sqrt (k + 1 : ℝ) * ((Real.sqrt (k.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly k x) * Aux_w_53_hermite.phi x +
            ((Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹) * Aux_w_53_hermite.Hpoly (k + 1) x * (-x * Aux_w_53_hermite.phi x)) := by
            rw [hfac2]
      _ = ((k + 1 : ℝ) * (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly k x -
            x * (Real.sqrt (k + 1 : ℝ))⁻¹ * (Real.sqrt (k.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (k + 1) x) * Aux_w_53_hermite.phi x := by
            rw [hsq]; ring
      _ = ((k + 1 : ℝ) * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly k x -
            x * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (k + 1) x) * Aux_w_53_hermite.phi x := by
            rw [hfac2]; ring
      _ = -((Real.sqrt (k + 2 : ℝ) * (Real.sqrt (k + 2 : ℝ))⁻¹) * (Real.sqrt ((k + 1).factorial : ℝ))⁻¹ *
            (x * Aux_w_53_hermite.Hpoly (k + 1) x - (k + 1 : ℝ) * Aux_w_53_hermite.Hpoly k x)) * Aux_w_53_hermite.phi x := by
            rw [hsqrt_cancel]; ring
      _ = _ := by ring
