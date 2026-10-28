-- Prove2me | solution 1 for BitDFT.caller_ready_with_precision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:31:51.626576+00:00
-- url     : https://prove2.me/submissions/a9703d26-6dba-4f92-a0f4-99145af0e140

import Definitions.Def_BitDFT_CallerReady
import Theorems.Thm_BitDFT_vector_encoding_length
import Mathlib.Tactic.Linarith
import Theorems.Thm_BitDFT_prepare_call_with_precision
import Theorems.Thm_BitDFT_bank_head_setup_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

noncomputable section
open BitDFT.CallerReady BitDFT IntMul MachineSequence

private theorem input_length (n b : ℕ) (hn : 1 ≤ n) (U : Fin n → ℤ × ℤ) :
    (fourierInput (guardPrecision n b) U).length ≤ 12*n*guardPrecision n b := by
  let q := guardPrecision n b
  have hq : 1 ≤ q := by unfold q guardPrecision; omega
  have hnsize : n.size ≤ lg n+1 := by
    apply Nat.size_le.mpr
    have hnp : n ≤ 2^lg n := (Nat.le_pow_clog (by decide : 1<2) n).trans
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
    have hpos := Nat.two_pow_pos (lg n)
    rw [pow_succ]
    omega
  have hns : n.size ≤ q := by unfold q guardPrecision; omega
  have hqs : q.size ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  have hlenr : (encVector (q+1) U).length = 2*n*(q+2) := by
    simpa [Nat.add_assoc] using BitDFT.vector_encoding_length (q+1) U
  have hl : (fourierInput q U).length = 2*n.size+1+(2*q.size+1)+2*n*(q+2) := by
    simp only [fourierInput,List.length_append,hlenr]
    simp [encNat,bin]
    omega
  change (fourierInput q U).length ≤ 12*n*q
  rw [hl]
  have hnq : n ≤ n*q := by nlinarith
  have hqn : q ≤ n*q := by nlinarith
  have hp : 1 ≤ n*q := by nlinarith
  nlinarith

theorem solution (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let w := fourierInput q U
    ∃ t v, t ≤ 71*n*q ∧ BinaryCounter.value v = q ∧
      (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
        final N r (RewriteInput.final n b (encVector (q+1) U) v) w ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells (machine N r).outTape =
        (machine N r).tapeOf ([(machine N r).blank]++w.map (machine N r).bitSym++[(machine N r).sep]) ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head (machine N r).outTape = 1 ∧
      (∀ i : Fin (machine N r).k, 2 ≤ i.val → i.val < r+2 →
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells i = N.tapeOf [] ∧
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head i = 1) := by
  dsimp only
  let q := guardPrecision n b
  let w := fourierInput q U
  obtain ⟨s,v,hs,hv,hr,hout,hhead,hfresh⟩ := BitDFT.prepare_call_with_precision N r n b hn hb U
  let c := RewriteInput.final n b (encVector (q+1) U) v
  let f := PrepareCall.final N r c w
  have hhalt : ((preparation N r).step^[s] ((preparation N r).initCfg (requestedInput b U) [])).state =
      (native (preparation N r)).exit := by
    rw [hr]
    rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound
    (native (preparation N r)) (headControl N r)
    ((preparation N r).initCfg (requestedInput b U) []) s 1 hhalt
  change (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
    rightCfg (native (preparation N r)) (headControl N r)
      ((headControl N r).machine.step^[1]
        (handoff (native (preparation N r)) (headControl N r)
          ((preparation N r).step^[s] ((preparation N r).initCfg (requestedInput b U) [])))) at he
  rw [hr] at he
  change (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
    rightCfg (native (preparation N r)) (headControl N r)
      ((headControl N r).machine.step (BankHeadSetup.start (preparation N r) r f)) at he
  obtain ⟨hstep,hcells,hbanks,hin,houth⟩ := BitDFT.bank_head_setup_correct (preparation N r) r f
  rw [hstep] at he
  refine ⟨t,v,?_,hv,he,?_,?_,?_⟩
  · have hl := input_length n b hn U
    have hq : 1 ≤ guardPrecision n b := by unfold guardPrecision; omega
    have hp : 1 ≤ n*guardPrecision n b := by nlinarith
    nlinarith
  · exact hout
  · exact houth.trans hhead
  · intro i hlo hhi
    have hf := hfresh i hlo hhi
    exact ⟨hf.1,hbanks i hlo hhi hf.2⟩
