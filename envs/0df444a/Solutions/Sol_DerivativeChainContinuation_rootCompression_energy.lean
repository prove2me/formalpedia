-- Prove2me | solution 1 for DerivativeChainContinuation.rootCompression_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:28:52.696426+00:00
-- url     : https://prove2.me/submissions/2d53d7f0-520f-4248-a170-e57b891433d9

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix











theorem rootCompression_apply {n : ℕ} (a : Fin n → ℂ) (hc : ∑ i, a i = 0)
    (i j : Fin n) :
    rootCompression a i j = (if i=j then a i else 0) - (a i + a j)/(n : ℂ) := by
  unfold rootCompression centeringProjection
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.mul_apply, Matrix.of_apply]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  simp [hc]
  ring





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    frobeniusSq (rootCompression a) = ((n : ℝ)-2)*secondMoment a := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hre : ∑ i, (a i).re = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hc
  have him : ∑ i, (a i).im = 0 := by
    simpa only [Complex.im_sum, Complex.zero_im] using congrArg Complex.im hc
  have hs (i : Fin n) : (∑ j, Complex.normSq (a i+a j)) =
      (n : ℝ)*Complex.normSq (a i)+∑ j, Complex.normSq (a j) := by
    simp only [Complex.normSq_add, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      mul_neg, sub_neg_eq_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hre, him, mul_comm]
  have he (i j : Fin n) : Complex.normSq (rootCompression a i j) =
      (if i=j then Complex.normSq (a i)*(1-4/(n : ℝ)) else 0) +
        Complex.normSq (a i+a j)/(n : ℝ)^2 := by
    rw [rootCompression_apply a hc]
    by_cases hij : i=j
    · subst j
      simp only [if_pos rfl]
      simp [Complex.normSq_sub, Complex.normSq_div, Complex.normSq_apply,
        Complex.div_re, Complex.div_im, Complex.mul_re, Complex.conj_re,
        Complex.conj_im]
      field_simp
      ring
    · simp [hij, Complex.normSq_div, Complex.normSq_apply, pow_two]
      field_simp
  simp only [frobeniusSq, he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.sum_div, hs]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, secondMoment]
  field_simp
  ring
