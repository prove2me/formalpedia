-- Prove2me | solution 1 for DerivativeChainContinuation.monicDerivative_centered
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:07:37.258886+00:00
-- url     : https://prove2.me/submissions/3bbca5dd-3d81-4a74-a0d4-e3eba5fa01ab

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem monicDerivative_monic (p : Polynomial ℂ) (hp : p.Monic)
    (hn : p.natDegree ≠ 0) : (monicDerivative p).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_derivative, hp.leadingCoeff, one_mul]
  exact inv_mul_cancel₀ (by exact_mod_cast hn)

theorem monicDerivative_natDegree (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (monicDerivative p).natDegree = p.natDegree - 1 := by
  rw [monicDerivative, natDegree_C_mul (inv_ne_zero (by exact_mod_cast hn)),
    natDegree_derivative]






end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    (monicDerivative p).roots.sum = 0 := by
  have hn : p.natDegree ≠ 0 := by omega
  have hq := monicDerivative_monic p hp hn
  have hqd : (monicDerivative p).natDegree = n+2 := by
    rw [monicDerivative_natDegree p hn, hdeg]; omega
  have hc : p.coeff (n+2) = 0 := by
    have h := (IsAlgClosed.splits p).nextCoeff_eq_neg_sum_roots_of_monic hp
    rw [hcenter, neg_zero, nextCoeff_of_natDegree_pos (by omega), hdeg] at h
    simpa using h
  have hs := (IsAlgClosed.splits (monicDerivative p)).nextCoeff_eq_neg_sum_roots_of_monic hq
  rw [nextCoeff_of_natDegree_pos (by omega), hqd] at hs
  have hcoeff : (monicDerivative p).coeff (n+1) = 0 := by
    simp [monicDerivative, coeff_C_mul, coeff_derivative, hc, show n+1+1=n+2 by omega]
  have idx : n+2-1=n+1 := by omega
  rw [idx, hcoeff] at hs
  exact neg_eq_zero.mp hs.symm
