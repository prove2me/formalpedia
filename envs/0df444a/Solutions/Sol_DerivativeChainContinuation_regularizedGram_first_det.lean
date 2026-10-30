-- Prove2me | solution 1 for DerivativeChainContinuation.regularizedGram_first_det
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:24:36.024928+00:00
-- url     : https://prove2.me/submissions/6800eb9b-ec19-4bd8-8a17-6dd5763360f6

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FirstGramBlock
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_regularizedGram_first_blocks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hcol : ∀ i : Fin n,T i.succ 0=0) (t : ℝ) (ht : 0 < t) :
    (regularizedGram T t).det =
      ((t+Complex.normSq (T 0 0):ℝ):ℂ)*
        (regularizedGram (T.submatrix Fin.succ Fin.succ) t+
          ((t/(t+Complex.normSq (T 0 0)):ℝ):ℂ) •
            vecMulVec (fun i : Fin n => star (T 0 i.succ)) (fun j : Fin n => T 0 j.succ)).det := by
  let c : ℂ := (t:ℂ)+(Complex.normSq (T 0 0):ℂ)
  have hc : c ≠ 0 := by
    have h : 0 < t+Complex.normSq (T 0 0) := add_pos_of_pos_of_nonneg ht (Complex.normSq_nonneg _)
    simpa only [c,← Complex.ofReal_add] using Complex.ofReal_ne_zero.mpr h.ne'
  let A : Matrix Unit Unit ℂ := Matrix.of (fun _ _ => c)
  let B : Matrix Unit (Fin n) ℂ := Matrix.of (fun _ j => star (T 0 0)*T 0 j.succ)
  let C : Matrix (Fin n) Unit ℂ := Matrix.of (fun i _ => star (T 0 i.succ)*T 0 0)
  let D := regularizedGram (T.submatrix Fin.succ Fin.succ) t+
    vecMulVec (fun i : Fin n => star (T 0 i.succ)) (fun j : Fin n => T 0 j.succ)
  letI : Invertible A := ⟨Matrix.of (fun _ _ => c⁻¹),by
    ext i j
    cases i; cases j
    simp [A,Matrix.mul_apply,hc],by
    ext i j
    cases i; cases j
    simp [A,Matrix.mul_apply,hc]⟩
  have hinv : (⅟A : Matrix Unit Unit ℂ)=Matrix.of (fun _ _ => c⁻¹) := rfl
  have hblocks : (regularizedGram T t).submatrix (firstSumEquiv n) (firstSumEquiv n)=fromBlocks A B C D :=
    regularizedGram_first_blocks n T hcol t
  rw [← det_submatrix_equiv_self (firstSumEquiv n) (regularizedGram T t),hblocks,
    det_fromBlocks₁₁,det_unique A,hinv]
  change c*(D-C*Matrix.of (fun _ _ : Unit => c⁻¹)*B).det=_
  have hschur : D-C*Matrix.of (fun _ _ : Unit => c⁻¹)*B =
      regularizedGram (T.submatrix Fin.succ Fin.succ) t+
        ((t/(t+Complex.normSq (T 0 0)):ℝ):ℂ) •
          vecMulVec (fun i : Fin n => star (T 0 i.succ)) (fun j : Fin n => T 0 j.succ) := by
    ext i j
    simp only [D,Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply,Matrix.of_apply,
      Fintype.sum_unique,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,B,C,
      Complex.ofReal_div,Complex.ofReal_add]
    have hnorm : (Complex.normSq (T 0 0):ℂ)=star (T 0 0)*T 0 0 := by
      simp only [Complex.normSq_eq_conj_mul_self,Complex.star_def]
    change _ = _+((t:ℂ)/c)*_
    field_simp [hc]
    dsimp [c]
    rw [hnorm]
    simp only [Complex.star_def]
    ring
  rw [hschur]
  simp only [c,Complex.ofReal_add]
