-- Prove2me | solution 1 for DerivativeChainContinuation.covariance_moment_formula
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:56:02.055042+00:00
-- url     : https://prove2.me/submissions/88f83db5-a881-4065-93cc-8cfaeea99738

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {n : ℕ} (a : Fin n → ℂ) :
    covariance a =
      !![(secondMoment a + (holomorphicMoment a).re)/2, (holomorphicMoment a).im/2;
         (holomorphicMoment a).im/2, (secondMoment a - (holomorphicMoment a).re)/2] := by
  by_cases hn0 : n = 0
  · subst n
    simp [covariance, secondMoment, holomorphicMoment]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hsq (z : ℂ) : (z^2).re = z.re^2-z.im^2 := by simp [pow_two]
  have hsi (z : ℂ) : (z^2).im = 2*z.re*z.im := by simp [pow_two]; ring
  have hn (z : ℂ) : Complex.normSq z = z.re^2+z.im^2 := by
    simp [Complex.normSq_apply, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covariance, secondMoment, holomorphicMoment, Complex.mul_re, Complex.mul_im,
      hsq, hsi, hn, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, div_eq_mul_inv] <;> field_simp [hnR] <;> ring_nf <;> simp [Finset.sum_mul]
