-- Prove2me | solution 1 for Aux_w_53_hermite.h1D_orthonormal_aux
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:14.143721+00:00
-- url     : https://prove2.me/submissions/1b0d8cd1-7dc0-498a-926f-0c1d53ba0348

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
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D_mul_phi
import Theorems.Thm_Aux_w_53_hermite_tendsto_pow_mul_phi_atTop
section
set_option autoImplicit false

namespace Aux_w_53_hermite

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density, Orthonormal Hermite Functions, and `sgn` Coefficients -/







lemma phi_neg (x : ℝ) : phi (-x) = phi x := by
  simp [phi_def]

















































lemma tendsto_pow_mul_phi_atBot (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * phi x) atBot (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (-1 : ℝ) ^ k * ((-x) ^ k * phi (-x))) atBot (𝓝 ((-1 : ℝ) ^ k * 0)) :=
    ((tendsto_pow_mul_phi_atTop k).comp tendsto_neg_atBot_atTop).const_mul ((-1 : ℝ) ^ k)
  rw [mul_zero] at h1
  refine h1.congr fun x => ?_
  rw [phi_neg, neg_pow x k]
  calc (-1 : ℝ) ^ k * (((-1 : ℝ) ^ k * x ^ k) * phi x)
      = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (x ^ k * phi x) := by ring
    _ = 1 * (x ^ k * phi x) := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    _ = x ^ k * phi x := one_mul _

lemma tendsto_poly_mul_phi_atTop (P : Polynomial ℝ) :
    Tendsto (fun x : ℝ => P.eval x * phi x) atTop (𝓝 0) := by
  have hsum : (fun x : ℝ => P.eval x * phi x) =
      fun x => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x) := by
    ext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have hlim : Tendsto (fun x : ℝ => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x)) atTop
      (𝓝 (∑ i ∈ P.support, (P.coeff i) * 0)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_pow_mul_phi_atTop i).const_mul _
  simpa using hlim

lemma tendsto_poly_mul_phi_atBot (P : Polynomial ℝ) :
    Tendsto (fun x : ℝ => P.eval x * phi x) atBot (𝓝 0) := by
  have hsum : (fun x : ℝ => P.eval x * phi x) =
      fun x => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x) := by
    ext x
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have hlim : Tendsto (fun x : ℝ => ∑ i ∈ P.support, (P.coeff i) * (x ^ i * phi x)) atBot
      (𝓝 (∑ i ∈ P.support, (P.coeff i) * 0)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_pow_mul_phi_atBot i).const_mul _
  simpa using hlim

lemma integral_poly_mul_h1D_succ (P : Polynomial ℝ) (m : ℕ) :
    ∫ x : ℝ, P.eval x * h1D (m + 1) x * phi x =
      (Real.sqrt (m + 1 : ℝ))⁻¹ * ∫ x : ℝ, P.derivative.eval x * h1D m x * phi x := by
  let F : ℝ → ℝ := fun x => P.eval x * (h1D m x * phi x)
  let F' : ℝ → ℝ := fun x =>
    P.derivative.eval x * h1D m x * phi x - Real.sqrt (m + 1 : ℝ) * (P.eval x * h1D (m + 1) x * phi x)
  have hderiv : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    have h := (P.hasDerivAt x).mul (hasDerivAt_h1D_mul_phi m x)
    refine h.congr_deriv ?_
    simp only [F']
    ring
  let Q : Polynomial ℝ :=
    P * (Polynomial.C (Real.sqrt (m.factorial : ℝ))⁻¹ * (Polynomial.hermite m).map (algebraMap ℤ ℝ))
  have hF_eq : F = fun x => Q.eval x * phi x := by
    ext x
    simp only [F, Q, h1D, Hpoly, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.aeval_def, Polynomial.eval_map]
    ring
  have h1_int : Integrable (fun x => P.derivative.eval x * h1D m x * phi x) volume := by
    have h := integrable_poly_mul_phi (P.derivative * (Polynomial.C (Real.sqrt (m.factorial : ℝ))⁻¹ *
      (Polynomial.hermite m).map (algebraMap ℤ ℝ)))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
  have h2_int : Integrable (fun x => P.eval x * h1D (m + 1) x * phi x) volume := by
    have h := integrable_poly_mul_phi (P * (Polynomial.C (Real.sqrt ((m + 1).factorial : ℝ))⁻¹ *
      (Polynomial.hermite (m + 1)).map (algebraMap ℤ ℝ)))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp [h1D, Hpoly, Polynomial.aeval_def, Polynomial.eval_map, mul_assoc]
  have hF'_int : Integrable F' volume := h1_int.sub (h2_int.const_mul _)
  have hint := integral_of_hasDerivAt_of_tendsto hderiv hF'_int
    (hF_eq ▸ tendsto_poly_mul_phi_atBot Q) (hF_eq ▸ tendsto_poly_mul_phi_atTop Q)
  rw [sub_self] at hint
  have hsub : ∫ x : ℝ, F' x =
      (∫ x : ℝ, P.derivative.eval x * h1D m x * phi x) -
      Real.sqrt (m + 1 : ℝ) * (∫ x : ℝ, P.eval x * h1D (m + 1) x * phi x) := by
    simp only [F']
    rw [integral_sub h1_int (h2_int.const_mul _), integral_const_mul]
  rw [hsub] at hint
  have hsqrt_ne : Real.sqrt (m + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have heq : Real.sqrt (m + 1 : ℝ) * (∫ x : ℝ, P.eval x * h1D (m + 1) x * phi x) =
      ∫ x : ℝ, P.derivative.eval x * h1D m x * phi x := by linarith
  rw [← heq, ← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]





















/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/





























end Aux_w_53_hermite


end
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal
theorem solution (j k : ℕ) :
    ∫ x : ℝ, Aux_w_53_hermite.h1D j x * Aux_w_53_hermite.h1D k x * Aux_w_53_hermite.phi x = if j = k then 1 else 0 := by
  wlog hjk : j ≤ k generalizing j k
  · have hkj : k ≤ j := Nat.le_of_not_ge hjk
    have hsym : (fun x : ℝ => Aux_w_53_hermite.h1D j x * Aux_w_53_hermite.h1D k x * Aux_w_53_hermite.phi x) = fun x => Aux_w_53_hermite.h1D k x * Aux_w_53_hermite.h1D j x * Aux_w_53_hermite.phi x := by
      ext x; ring
    rw [hsym, this k j hkj]
    simp [eq_comm]
  induction k generalizing j with
  | zero =>
    have hj : j = 0 := by omega
    subst hj
    simp only [↓reduceIte, Aux_w_53_hermite.h1D_zero_fn, one_mul]
    exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  | succ k ih =>
    let P : Polynomial ℝ :=
      Polynomial.C (Real.sqrt (j.factorial : ℝ))⁻¹ * (Polynomial.hermite j).map (algebraMap ℤ ℝ)
    have hP : ∀ x, Aux_w_53_hermite.h1D j x = P.eval x := by
      intro x; simp [P, Aux_w_53_hermite.h1D, Aux_w_53_hermite.Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
    simp_rw [hP]
    rw [Aux_w_53_hermite.integral_poly_mul_h1D_succ P k]
    cases j with
    | zero =>
      have : P.derivative = 0 := by simp [P]
      simp [this]
    | succ m =>
      have hPderiv : ∀ x, P.derivative.eval x = Real.sqrt (m + 1 : ℝ) * Aux_w_53_hermite.h1D m x := by
        intro x
        simp only [P, Polynomial.derivative_C_mul, Polynomial.derivative_map,
          Aux_w_53_hermite.derivative_hermite m, Polynomial.map_mul, Polynomial.eval_mul, Polynomial.eval_C,
          Aux_w_53_hermite.h1D, Aux_w_53_hermite.Hpoly, Polynomial.aeval_def, Polynomial.eval_map]
        have hfac : (Real.sqrt ((m + 1).factorial : ℝ))⁻¹ =
            (Real.sqrt (m + 1 : ℝ))⁻¹ * (Real.sqrt (m.factorial : ℝ))⁻¹ := by
          rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv]
          rw [show (((m + 1 : ℕ) : ℝ)) = m + 1 by push_cast; ring, mul_comm]
        have hp : (0 : ℝ) < m + 1 := by positivity
        have hsq : (m + 1 : ℝ) * (Real.sqrt (m + 1 : ℝ))⁻¹ = Real.sqrt (m + 1 : ℝ) := by
          rw [eq_comm, eq_mul_inv_iff_mul_eq₀ (Real.sqrt_ne_zero'.mpr hp), Real.mul_self_sqrt hp.le]
        rw [hfac, Polynomial.eval₂_C]
        simp only [eq_intCast, Int.cast_natCast]
        push_cast
        calc (Real.sqrt (m + 1 : ℝ))⁻¹ * (Real.sqrt (m.factorial : ℝ))⁻¹ *
              ((m + 1 : ℝ) * Polynomial.eval₂ (algebraMap ℤ ℝ) x (Polynomial.hermite m))
            = ((m + 1 : ℝ) * (Real.sqrt (m + 1 : ℝ))⁻¹) * ((Real.sqrt (m.factorial : ℝ))⁻¹ *
                Polynomial.eval₂ (algebraMap ℤ ℝ) x (Polynomial.hermite m)) := by ring
          _ = Real.sqrt (m + 1 : ℝ) * ((Real.sqrt (m.factorial : ℝ))⁻¹ *
                Polynomial.eval₂ (algebraMap ℤ ℝ) x (Polynomial.hermite m)) := by rw [hsq]
      simp_rw [hPderiv]
      have hmul : (fun x => Real.sqrt (m + 1 : ℝ) * Aux_w_53_hermite.h1D m x * Aux_w_53_hermite.h1D k x * Aux_w_53_hermite.phi x) =
          fun x => Real.sqrt (m + 1 : ℝ) * (Aux_w_53_hermite.h1D m x * Aux_w_53_hermite.h1D k x * Aux_w_53_hermite.phi x) := by ext x; ring
      rw [hmul, integral_const_mul]
      have hmle : m ≤ k := by omega
      rw [ih m hmle]
      rcases eq_or_lt_of_le hmle with rfl | hlt
      · simp only [↓reduceIte, mul_one]
        have hne : Real.sqrt (m + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
        rw [inv_mul_cancel₀ hne]
      · have hne1 : m ≠ k := hlt.ne
        simp [hne1]
