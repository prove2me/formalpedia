-- Prove2me | solution 1 for BitDFT.prepare_call_with_precision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:29:22.477979+00:00
-- url     : https://prove2.me/submissions/4a4fef63-ad6e-4198-83fa-aa3ba0b09c6e

import Definitions.Def_BitDFT_PrepareCall
import Theorems.Thm_BitDFT_preprocessor_placement_with_precision
import Theorems.Thm_BitDFT_buffer_shift_on_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

noncomputable section
namespace BitDFT.PrepareCall
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem correct_handoff (N : MultitapeTM) (r n b : ℕ) (U : Fin n → ℤ × ℤ) (v : List Bool) :
    shiftBase N r (RewriteInput.final n b (encVector (guardPrecision n b+1) U) v) =
      shiftStart N r (RewriteInput.final n b (encVector (guardPrecision n b+1) U) v)
        (fourierInput (guardPrecision n b) U) := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < 2
    · have hz : i.val = 0 ∨ i.val = 1 := by omega
      rcases hz with hz | hz
      · have he : i = ⟨0,by have := (preprocess N r).two_le_k; omega⟩ := Fin.ext hz
        rw [he]
        rfl
      · have he : i = ⟨1,by have := (preprocess N r).two_le_k; omega⟩ := Fin.ext hz
        rw [he]
        rfl
    · simp only [shiftStart,BufferShiftOn.embed,hi,dite_false]
  · funext i
    by_cases hi : i.val < 2
    · have hz : i.val = 0 ∨ i.val = 1 := by omega
      rcases hz with hz | hz
      · have he : i = ⟨0,by have := (preprocess N r).two_le_k; omega⟩ := Fin.ext hz
        rw [he]
        rfl
      · have he : i = ⟨1,by have := (preprocess N r).two_le_k; omega⟩ := Fin.ext hz
        rw [he]
        rfl
    · simp only [shiftStart,BufferShiftOn.embed,hi,dite_false]

theorem shift_run (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (shiftControl N r).machine.step^[3*w.length+5] (shiftStart N r c w) = shiftFinish N r c w := by
  exact (BitDFT.buffer_shift_on_correct (preprocess N r) (shiftBase N r c) (smallBase c) w).1


private theorem tape_encode (N : MultitapeTM) (out : List BufferShift.machine.Sym) :
    (fun p => (BufferShiftOn.alphabetMap N).encode (BufferShift.machine.tapeOf out p)) =
      (BufferShiftOn.small N).tapeOf (out.map (BufferShiftOn.alphabetMap N).encode) := by
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    simp [MultitapeTM.tapeOf]
    cases h : out[p]? <;> simp [h,BufferShiftOn.alphabetMap,PreprocessorAlphabet.alphabetMap,PreprocessorAlphabet.encode] <;> rfl

theorem final_output (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (final N r c w).cells (machine N r).outTape =
      (machine N r).tapeOf ([(machine N r).blank]++w.map (machine N r).bitSym++[(machine N r).sep]) := by
  have h := tape_encode (preprocess N r) ([.blank]++w.map BufferShift.machine.bitSym++[.sep])
  have hm : ([BufferShift.machine.blank]++w.map BufferShift.machine.bitSym++[BufferShift.machine.sep]).map
      (BufferShiftOn.alphabetMap (preprocess N r)).encode =
      [(machine N r).blank]++w.map (machine N r).bitSym++[(machine N r).sep] := by
    simp only [List.map_append,List.map_cons,List.map_nil,List.map_map]
    have hb : (fun a => (BufferShiftOn.alphabetMap (preprocess N r)).encode a) ∘ BufferShift.machine.bitSym =
        (machine N r).bitSym := by
      funext b
      cases b <;> rfl
    rw [hb]
    rfl
  rw [hm] at h
  exact h

theorem final_head (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (final N r c w).head (machine N r).outTape = 1 := by rfl

theorem final_workspace (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool)
    (i : Fin (machine N r).k) (hi : 2 ≤ i.val) :
    (final N r c w).cells i = (PreprocessorPlacement.embed N r c).cells i ∧
      (final N r c w).head i = (PreprocessorPlacement.embed N r c).head i := by
  simp [final,rightCfg,shiftFinish,BufferShiftOn.embed,shiftBase,handoff,show ¬i.val≤1 by omega]

end BitDFT.PrepareCall
open BitDFT.PrepareCall BitDFT IntMul MachineSequence

theorem solution (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let w := fourierInput q U
    ∃ t v, t ≤ 27*n*q+3*w.length+6 ∧ BinaryCounter.value v = q ∧
      (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
        final N r (RewriteInput.final n b (encVector (q+1) U) v) w ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells (machine N r).outTape =
        (machine N r).tapeOf ([(machine N r).blank]++w.map (machine N r).bitSym++[(machine N r).sep]) ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head (machine N r).outTape = 1 ∧
      (∀ i : Fin (machine N r).k, 2 ≤ i.val → i.val < r+2 →
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells i = N.tapeOf [] ∧
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head i = 0) := by
  dsimp only
  let q := guardPrecision n b
  let w := fourierInput q U
  obtain ⟨s,v,hs,hv,hr,hhalt,_,_,hfresh⟩ := BitDFT.preprocessor_placement_with_precision N r n b hn hb U
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound
    (native (preprocess N r)) (shiftControl N r)
    ((preprocess N r).initCfg (requestedInput b U) []) s (3*w.length+5) hhalt
  change (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
    rightCfg (native (preprocess N r)) (shiftControl N r)
      ((shiftControl N r).machine.step^[3*w.length+5]
        (handoff (native (preprocess N r)) (shiftControl N r)
          ((preprocess N r).step^[s] ((preprocess N r).initCfg (requestedInput b U) [])))) at he
  rw [hr] at he
  change (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
    rightCfg (native (preprocess N r)) (shiftControl N r)
      ((shiftControl N r).machine.step^[3*w.length+5]
        (shiftBase N r (RewriteInput.final n b (encVector (q+1) U) v))) at he
  rw [correct_handoff,shift_run] at he
  refine ⟨t,v,?_,hv,he,final_output N r _ w,final_head N r _ w,?_⟩
  · dsimp [w,q] at ht
    omega
  · intro i hlo hhi
    have hf := hfresh i hlo hhi
    rw [hr] at hf
    have hw := final_workspace N r (RewriteInput.final n b (encVector (q+1) U) v) w i hlo
    exact ⟨hw.1.trans hf.1,hw.2.trans hf.2⟩
