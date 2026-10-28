-- Prove2me | solution 1 for BitDFT.request_preprocessor_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:44:47.728534+00:00
-- url     : https://prove2.me/submissions/fe56c3b3-867b-429f-8d02-2c5bdba51c0d

import Theorems.Thm_BitDFT_rewrite_input_correct
import Theorems.Thm_BitDFT_vector_encoding_length
import Mathlib.Tactic.Linarith

open BitDFT IntMul

theorem solution (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    Computes RewriteInput.machine (requestedInput b U) (fourierInput (guardPrecision n b) U)
      (27 * (n : ℝ) * (guardPrecision n b : ℝ)) := by
  let q := guardPrecision n b
  obtain ⟨t,v,ht,hv,hlen,hr⟩ := BitDFT.rewrite_input_correct n b hn hb (encVector (q+1) U)
  have hq : 1 ≤ q := by unfold q guardPrecision; omega
  have hlenr : (encVector (q+1) U).length = 2*n*(q+2) := by
    simpa [Nat.add_assoc] using BitDFT.vector_encoding_length (q+1) U
  rw [hlenr] at ht
  have ht' : t ≤ 27*n*q := by
    have hqn : q ≤ n*q := by nlinarith
    have hnq : n ≤ n*q := by nlinarith
    have hnqpos : 1 ≤ n*q := by nlinarith
    change t ≤ 19*q+2*n*(q+2)+2 at ht
    nlinarith
  refine ⟨t,?_,?_,?_⟩
  · exact_mod_cast ht'
  · change (RewriteInput.machine.step^[t]
      (RewriteInput.machine.initCfg (encNat n++encNat b++encVector (q+1) U) [])).state = _
    rw [hr]
    rfl
  · change (RewriteInput.machine.step^[t]
      (RewriteInput.machine.initCfg (encNat n++encNat b++encVector (q+1) U) [])).cells 1 = _
    rw [hr]
    rfl
