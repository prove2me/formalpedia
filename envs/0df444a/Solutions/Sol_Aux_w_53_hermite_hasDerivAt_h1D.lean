-- Prove2me | solution 1 for Aux_w_53_hermite.hasDerivAt_h1D
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:02.906666+00:00
-- url     : https://prove2.me/submissions/dd8cf1c7-f83f-45ee-9d77-72e9a795551f

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





















lemma hasDerivAt_Hpoly_succ (j : ℕ) (x : ℝ) :
    HasDerivAt (Hpoly (j + 1)) ((j + 1 : ℝ) * Hpoly j x) x := by
  let P : ℝ[X] := (Polynomial.hermite (j + 1)).map (algebraMap ℤ ℝ)
  have hP : HasDerivAt (fun y => P.eval y) (P.derivative.eval x) x := P.hasDerivAt x
  have h1 : (fun y => P.eval y) = Hpoly (j + 1) := by
    ext y; simp [P, Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  have h2 : P.derivative.eval x = (j + 1 : ℝ) * Hpoly j x := by
    dsimp [P]
    rw [Polynomial.derivative_map, derivative_hermite]
    simp [Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
  rwa [h1, h2] at hP































































/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/





























end Aux_w_53_hermite


end
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal
theorem solution (j : ℕ) (x : ℝ) : HasDerivAt (Aux_w_53_hermite.h1D j) (Aux_w_53_hermite.h1D_deriv j x) x := by
  cases j with
  | zero =>
    have : Aux_w_53_hermite.h1D 0 = fun _ => 1 := funext Aux_w_53_hermite.h1D_zero_fn
    rw [this, Aux_w_53_hermite.h1D_deriv]
    simp [hasDerivAt_const]
  | succ j =>
    have h := (Aux_w_53_hermite.hasDerivAt_Hpoly_succ j x).const_mul (Real.sqrt ((j + 1).factorial : ℝ))⁻¹
    have hfn : (fun y => (Real.sqrt ((j + 1).factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly (j + 1) y) = Aux_w_53_hermite.h1D (j + 1) := rfl
    rw [hfn] at h
    refine h.congr_deriv ?_
    simp only [Aux_w_53_hermite.h1D_deriv, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, Aux_w_53_hermite.h1D, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hpos : (0 : ℝ) < j + 1 := by positivity
    rw [Real.sqrt_mul hpos.le, mul_inv]
    have hsq : (j + 1 : ℝ) * (Real.sqrt (j + 1 : ℝ))⁻¹ = Real.sqrt (j + 1 : ℝ) := by
      rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (Real.sqrt_ne_zero'.mpr hpos), Real.mul_self_sqrt hpos.le]
    calc (Real.sqrt (j + 1 : ℝ))⁻¹ * (Real.sqrt (j.factorial : ℝ))⁻¹ * ((j + 1 : ℝ) * Aux_w_53_hermite.Hpoly j x)
        = ((j + 1 : ℝ) * (Real.sqrt (j + 1 : ℝ))⁻¹) * ((Real.sqrt (j.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly j x) := by ring
      _ = Real.sqrt (j + 1 : ℝ) * ((Real.sqrt (j.factorial : ℝ))⁻¹ * Aux_w_53_hermite.Hpoly j x) := by rw [hsq]
