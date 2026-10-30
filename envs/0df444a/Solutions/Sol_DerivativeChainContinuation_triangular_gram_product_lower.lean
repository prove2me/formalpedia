-- Prove2me | solution 1 for DerivativeChainContinuation.triangular_gram_product_lower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:26:46.139607+00:00
-- url     : https://prove2.me/submissions/1670b366-8f5e-4dfa-ae9e-d6f7be8a5b79

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_scaled_rank_one_determinant
import Theorems.Thm_DerivativeChainContinuation_regularizedGram_first_det
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators ComplexOrder





theorem regularizedGram_posDef {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (ht : 0 < t) : (regularizedGram T t).PosDef := by
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast ht
  · exact posSemidef_conjTranspose_mul_self T










end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsUpperTriangular) (t : ℝ) (ht : 0 < t) :
    (∏ j,(t+Complex.normSq (T j j))) ≤ ‖(regularizedGram T t).det‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    let B := T.submatrix Fin.succ Fin.succ
    have hB : B.IsUpperTriangular := by
      intro i j hji
      exact hT (Fin.succ_lt_succ_iff.mpr hji)
    have hcol (i : Fin n) : T i.succ 0=0 := hT (Fin.succ_pos i)
    have hc : 0 < t+Complex.normSq (T 0 0) := add_pos_of_pos_of_nonneg ht (Complex.normSq_nonneg _)
    have hmono := positive_scaled_rank_one_determinant (regularizedGram B t)
      (regularizedGram_posDef B t ht) (fun i => star (T 0 i.succ))
      (t/(t+Complex.normSq (T 0 0))) (div_nonneg ht.le hc.le)
    have hmono' : ‖(regularizedGram B t).det‖ ≤
        ‖(regularizedGram B t+((t/(t+Complex.normSq (T 0 0)):ℝ):ℂ) •
          vecMulVec (fun i : Fin n => star (T 0 i.succ)) (fun j : Fin n => T 0 j.succ)).det‖ := by
      have hf : star (fun i : Fin n => star (T 0 i.succ))=(fun j : Fin n => T 0 j.succ) := by
        funext i
        simp
      rwa [hf] at hmono
    have hib := ih B hB
    rw [Fin.prod_univ_succ,regularizedGram_first_det n T hcol t ht,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hib.trans hmono') hc.le
