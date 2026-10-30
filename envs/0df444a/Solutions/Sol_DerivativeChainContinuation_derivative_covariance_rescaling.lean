-- Prove2me | solution 1 for DerivativeChainContinuation.derivative_covariance_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:11:39.109811+00:00
-- url     : https://prove2.me/submissions/d5384e42-ccfa-4740-8cce-ef6b0f49defc

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_derivative_centered_second_moment
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





theorem monicDerivative_natDegree (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (monicDerivative p).natDegree = p.natDegree - 1 := by
  rw [monicDerivative, natDegree_C_mul (inv_ne_zero (by exact_mod_cast hn)),
    natDegree_derivative]






end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial









theorem derivative_holomorphic_rescaling (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    rootHolomorphicMoment (monicDerivative p) / (n+1 : ℂ) =
      rootHolomorphicMoment p / (n+2 : ℂ) := by
  have hn : p.natDegree ≠ 0 := by omega
  have hqd : (monicDerivative p).natDegree = n+2 := by
    rw [monicDerivative_natDegree p hn, hdeg]; omega
  have h := derivative_centered_second_moment p hp n hdeg hcenter
  have h1 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  have h2 : (n+2 : ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  have h3 : (n+3 : ℂ) ≠ 0 := by exact_mod_cast (show n+3 ≠ 0 by omega)
  simp only [rootHolomorphicMoment, hqd, hdeg, Nat.cast_add, Nat.cast_ofNat]
  field_simp
  linear_combination h




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    ((n+2 : ℝ)⁻¹ • rootCovariance p) -
      ((n+1 : ℝ)⁻¹ • rootCovariance (monicDerivative p)) =
      (schoenbergDeficit p / (2*(n+2)*(n+1) : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := derivative_holomorphic_rescaling p hp n hdeg hcenter
  have h1 : (n+1 : ℝ) ≠ 0 := by positivity
  have h2 : (n+2 : ℝ) ≠ 0 := by positivity
  have h1C : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  have h2C : (n+2 : ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  have hc := (div_eq_div_iff h1C h2C).mp h
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  norm_num [Complex.mul_re, Complex.mul_im] at hre him
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootCovariance, schoenbergDeficit, hdeg,
      show n+3-2=n+1 by omega, show n+3-1=n+2 by omega,
      Matrix.smul_apply, Matrix.sub_apply] <;>
    field_simp [h1,h2] <;> nlinarith [hre,him]
