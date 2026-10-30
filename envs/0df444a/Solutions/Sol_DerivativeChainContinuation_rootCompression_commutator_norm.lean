-- Prove2me | solution 1 for DerivativeChainContinuation.rootCompression_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:50:52.746989+00:00
-- url     : https://prove2.me/submissions/31265291-c3c9-4cfd-b8e5-b95027f53961

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_rootCompression_commutator_apply
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    frobeniusSq (rootCompression a * (rootCompression a).conjTranspose -
      (rootCompression a).conjTranspose * rootCompression a) = 8*(covariance a).det := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he (i j : Fin n) :
      Complex.normSq ((star (a i)*a j-a i*star (a j))/(n : ℂ)) =
        4*((a i).re*(a j).im-(a i).im*(a j).re)^2/(n : ℝ)^2 := by
    rw [map_div₀]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def,
      pow_two]
    ring
  simp only [frobeniusSq, rootCompression_commutator_apply hn a hc, he]
  rw [Matrix.det_fin_two]
  simp only [covariance, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hcross (i j : Fin n) :
      2*((a i).re*(a j).im)*((a i).im*(a j).re) =
        2*((a i).re*(a i).im)*((a j).re*(a j).im) := by ring
  simp only [sub_sq, mul_pow, hcross, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  simp only [← mul_assoc, ← Finset.sum_mul]
  field_simp
  ring_nf
  simp only [← Finset.sum_mul]
  ring
