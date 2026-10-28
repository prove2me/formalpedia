-- Prove2me | solution 1 for BitDFT.vector_ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:45:29.181025+00:00
-- url     : https://prove2.me/submissions/3ad01b07-a052-41a6-b8bf-62744399a970

import Definitions.Def_BitDFT_VectorReady
import Theorems.Thm_BitDFT_child_descriptor_output
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_output_length_le_time
import Mathlib.Tactic

namespace BitDFT.VectorReady
open IntMul MachineSequence
private theorem positive_not_marker (N : MultitapeTM) (w : List Bool) (p : ℕ) (hp : 0 < p) :
    N.tapeOf (w.map N.bitSym) p ≠ N.startSym := by
  have hd := N.syms_distinct
  simp [List.nodup_cons,List.mem_cons,not_or] at hd
  have hb : N.blank ≠ N.startSym := by aesop
  have hz : N.zero ≠ N.startSym := by aesop
  have ho : N.one ≠ N.startSym := by aesop
  cases p with
  | zero => omega
  | succ p =>
    simp only [MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h : w[p]? with
    | none => simpa [h] using hb
    | some b => cases b <;> simp [h,MultitapeTM.bitSym,hz,ho]

private theorem correct_handoff (M : MultitapeTM) (base : (preparation M).Cfg) (p : ℕ)
    (hp : base.head (preparation M).outTape = p) :
    handoff (native (preparation M)) (rewind M) base =
      RewindTape.frame (preparation M) (preparation M).outTape base false p := by
  have hh : Function.update base.head (preparation M).outTape p = base.head := by
    rw [← hp]
    exact Function.update_eq_self _ _
  change MultitapeTM.Cfg.mk _ _ _ = MultitapeTM.Cfg.mk _ _ (Function.update _ _ _)
  rw [hh]
  rfl
end BitDFT.VectorReady
open BitDFT.VectorReady BitDFT IntMul MachineSequence

theorem solution (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 193*n*q+11*T ∧ BinaryCounter.value v = q ∧
      (machine M).step^[t] ((machine M).initCfg (requestedInput b U) []) =
        final M (requestedInput b U)
          (NativeChildOutput.final M (ChildCall.final M
            (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w)
          (bin q.size q) ∧
      (machine M).HaltsWithOutput (requestedInput b U) [] t w ∧
      ((machine M).step^[t] ((machine M).initCfg (requestedInput b U) [])).head (machine M).outTape = 1 := by
  dsimp only
  let q := guardPrecision n b
  let input := requestedInput b U
  let x := fourierInput q U
  let y := bin q.size q
  obtain ⟨s,v,hs,hv,hr,hout,hhead⟩ := BitDFT.child_descriptor_output M n b hn hb U T halt w out
  let c := NativeChildOutput.final M (ChildCall.final M
    (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w
  let base := ChildDescriptor.final M input c y
  have hrun : (preparation M).step^[s] ((preparation M).initCfg input []) = base := hr
  have hbo : base.cells (preparation M).outTape = (preparation M).tapeOf (w.map (preparation M).bitSym) := by
    rw [← hrun]
    exact hout.2
  have hbh : base.head (preparation M).outTape = w.length+1 := by rw [← hrun]; exact hhead
  have hz : base.cells (preparation M).outTape 0 = (preparation M).startSym := by rw [hbo]; rfl
  have hnmark : ∀ p, 0 < p → base.cells (preparation M).outTape p ≠ (preparation M).startSym := by
    intro p hp
    rw [hbo]
    exact positive_not_marker _ _ _ hp
  have hrw := BitDFT.rewind_tape_correct (preparation M) (preparation M).outTape base hz hnmark (w.length+1)
  have hhalt : ((preparation M).step^[s] ((preparation M).initCfg input [])).state =
      (native (preparation M)).exit := hout.1
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (native (preparation M)) (rewind M)
    ((preparation M).initCfg input []) s (w.length+2) hhalt
  change (machine M).step^[t] ((machine M).initCfg input []) =
    rightCfg (native (preparation M)) (rewind M)
      ((rewind M).machine.step^[w.length+2] (handoff (native (preparation M)) (rewind M)
        ((preparation M).step^[s] ((preparation M).initCfg input [])))) at he
  rw [hrun,correct_handoff M base _ hbh] at he
  change (machine M).step^[t] ((machine M).initCfg input []) =
    rightCfg (native (preparation M)) (rewind M)
      ((RewindTape.machine (preparation M) (preparation M).outTape).step^[(w.length+1)+1]
        (RewindTape.frame (preparation M) (preparation M).outTape base false (w.length+1))) at he
  rw [hrw] at he
  change (machine M).step^[t] ((machine M).initCfg input []) = final M input c y at he
  refine ⟨t,v,?_,hv,he,?_,?_⟩
  · have hw := BitDFT.output_length_le_time M (fourierInput q U) [] w T ⟨halt,out⟩
    have hq : 1 ≤ q := by dsimp [q,guardPrecision]; omega
    have hnq : 1 ≤ n*q := by nlinarith
    change s ≤ 190*n*q+10*T at hs
    nlinarith
  · constructor
    · rw [he]; rfl
    · rw [he]
      exact hbo
  · rw [he]
    simp [final,MachineSequence.rightCfg,RewindTape.frame,MultitapeTM.outTape]
