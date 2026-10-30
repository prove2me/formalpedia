-- Prove2me | solution 1 for DerivativeChainContinuation.projection_vectorSq
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:46:30.748952+00:00
-- url     : https://prove2.me/submissions/5015c7e4-9570-4c3d-981e-3b3460484572

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_MatrixEnergy
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0) (v : Fin n → ℂ) :
    vectorSq (centeringProjection n *ᵥ v) =
      vectorSq v - Complex.normSq (∑ i, v i)/(n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he (i : Fin n) : (centeringProjection n *ᵥ v) i =
      v i-(∑ j, v j)/(n : ℂ) := by
    simp [centeringProjection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec,
      dotProduct, ← Finset.mul_sum, div_eq_mul_inv, mul_comm,
      mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, ← Finset.sum_mul]
  simp only [vectorSq, he, Complex.normSq_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul]
  simp [Complex.normSq_div, Complex.normSq_apply, Complex.mul_re,
    Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring
