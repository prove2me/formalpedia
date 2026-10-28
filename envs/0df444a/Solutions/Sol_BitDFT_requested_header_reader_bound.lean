-- Prove2me | solution 1 for BitDFT.requested_header_reader_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:00:34.756335+00:00
-- url     : https://prove2.me/submissions/fb68ab6a-2015-478f-8485-730c8b4c601a

import Theorems.Thm_BitDFT_header_reader_correct
import Theorems.Thm_BitDFT_vector_encoding_length
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open BitDFT
open IntMul

private lemma size_le_lg_add_one (n : ℕ) : n.size ≤ IntMul.lg n + 1 := by
  apply Nat.size_le.mpr
  have hn : n ≤ 2 ^ IntMul.lg n :=
    (Nat.le_pow_clog (by decide : 1 < 2) n).trans
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hp : 0 < 2 ^ IntMul.lg n := Nat.two_pow_pos _
  rw [pow_succ]
  omega

theorem solution (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b)
    (U : Fin n → ℤ × ℤ) :
    ∃ t : ℕ, (t : ℝ) ≤ 16 * (n : ℝ) * (guardPrecision n b : ℝ) ∧
      HeaderReader.machine.HaltsWithOutput (requestedInput b U) [] t
        (encNat b ++ encVector (guardPrecision n b + 1) U) ∧
      (HeaderReader.machine.step^[t]
        (HeaderReader.machine.initCfg (requestedInput b U) [])).cells 3 =
        HeaderReader.machine.tapeOf ((IntMul.bin n.size n).map HeaderReader.machine.bitSym) ∧
      (HeaderReader.machine.step^[t]
        (HeaderReader.machine.initCfg (requestedInput b U) [])).cells 2 =
        HeaderReader.machine.tapeOf [] := by
  let rest := encNat b ++ encVector (guardPrecision n b+1) U
  have hv : (IntMul.bin n.size n).length = n.size := by simp [IntMul.bin]
  have h := BitDFT.header_reader_correct (IntMul.bin n.size n) rest
  dsimp only at h
  rw [hv] at h
  have hx : List.replicate n.size true ++ false :: (IntMul.bin n.size n ++ rest) =
      requestedInput b U := by simp [requestedInput, encNat, rest, List.append_assoc]
  rw [hx] at h
  refine ⟨2*n.size+rest.length+4, ?_, h.1, h.2.1, h.2.2.1⟩
  have hnsize : n.size ≤ guardPrecision n b :=
    (size_le_lg_add_one n).trans (by unfold guardPrecision; omega)
  have hbsize : b.size ≤ guardPrecision n b := by
    have hs : b.size ≤ b := Nat.size_le.mpr (Nat.lt_two_pow_self)
    exact hs.trans (by unfold guardPrecision; omega)
  have hq : 1 ≤ guardPrecision n b := by unfold guardPrecision; omega
  have hrlen : rest.length = 2*b.size+1+2*n*(guardPrecision n b+2) := by
    simp [rest, encNat, IntMul.bin, vector_encoding_length]
    ring
  have hclock : 2*n.size+rest.length+4 ≤ 16*n*guardPrecision n b := by
    rw [hrlen]
    have hnq : guardPrecision n b ≤ n*guardPrecision n b := by nlinarith
    have hnq' : n ≤ n*guardPrecision n b := by nlinarith
    nlinarith
  exact_mod_cast hclock
