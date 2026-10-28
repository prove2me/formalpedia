-- Prove2me | solution 1 for BitDFT.native_child_output_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:39:25.813498+00:00
-- url     : https://prove2.me/submissions/c890f0f0-7b08-4e0a-ae6d-282181bd6fde

import Definitions.Def_BitDFT_NativeChildOutput
import Mathlib.Tactic.Linarith
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_BitDFT_child_call_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_output_length_le_time

noncomputable section
namespace BitDFT.NativeChildOutput
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem step_embed (M : MultitapeTM) (base : (preparation M).Cfg) (c : (child M).Cfg) :
    (machine M).step (embed M base c) = embed M base ((child M).step c) := by
  have hread : (fun j => (embed M base c).cells (oldTape M j)
      ((embed M base c).head (oldTape M j))) = (fun j => c.cells j (c.head j)) := by
    funext j
    simp [embed,oldTape,j.isLt]
  apply cfg_ext
  · change ((child M).δ c.state _).1 = ((child M).δ c.state _).1
    rw [hread]
  · funext i
    by_cases hi : i.val < (child M).k
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]
  · funext i
    by_cases hi : i.val < (child M).k
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]

theorem run_embed (M : MultitapeTM) (base : (preparation M).Cfg) (c : (child M).Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M base c) = embed M base ((child M).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

theorem embed_project (M : MultitapeTM) (base : (preparation M).Cfg) :
    embed M base (project M base) =
      MachineSequence.handoff (MachineSequence.native (preparation M)) (control M) base := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < (child M).k <;> simp [embed,project,oldTape,hi,MachineSequence.handoff]
  · funext i
    by_cases hi : i.val < (child M).k <;> simp [embed,project,oldTape,hi,MachineSequence.handoff]



theorem returned_output (M : MultitapeTM) (base : (ChildCall.preparation M).Cfg) (x : List Bool) (T : ℕ) (w : List Bool) :
    (ChildCall.final M base x T w).cells (ChildCall.program M).outTape =
      TrackedOutputReturn.bufferTape M (base.cells (ChildCall.preparation M).outTape) 1 w := by
  change TrackedOutputReturn.bufferTape M (base.cells (ChildCall.preparation M).outTape) 1 (w.take w.length) = _
  simp

theorem returned_head (M : MultitapeTM) (base : (ChildCall.preparation M).Cfg) (x : List Bool) (T : ℕ) (w : List Bool) :
    (ChildCall.final M base x T w).head (ChildCall.program M).outTape = w.length+2 := by
  change 1+w.length+1 = w.length+2
  omega

private theorem buffer_idempotent (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base 1 w) 1 w =
      TrackedOutputReturn.bufferTape M base 1 w := by
  funext p
  by_cases h : p < 1 <;> simp [TrackedOutputReturn.bufferTape,h]

theorem correct_handoff (M : MultitapeTM) (base : (ChildCall.preparation M).Cfg) (x : List Bool) (T : ℕ) (w : List Bool) :
    project M (ChildCall.final M base x T w) =
      TrackedOutputShift.rewindFrame M (project M (ChildCall.final M base x T w)) w (w.length+2) := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val = 1
    · have he : i = (child M).outTape := Fin.ext hi
      rw [he]
      change (ChildCall.final M base x T w).cells (ChildCall.program M).outTape =
        TrackedOutputReturn.bufferTape M ((ChildCall.final M base x T w).cells (ChildCall.program M).outTape) 1 w
      rw [returned_output]
      exact (buffer_idempotent M _ w).symm
    · simp [TrackedOutputShift.rewindFrame,hi]
  · funext i
    by_cases hi : i.val = 1
    · have he : i = (child M).outTape := Fin.ext hi
      rw [he]
      exact returned_head M base x T w
    · simp [TrackedOutputShift.rewindFrame,hi]

theorem shift_run (M : MultitapeTM) (base : (ChildCall.preparation M).Cfg) (x : List Bool) (T : ℕ) (w : List Bool) :
    (machine M).step^[4*w.length+4]
      (MachineSequence.handoff (MachineSequence.native (preparation M)) (control M) (ChildCall.final M base x T w)) =
      embed M (ChildCall.final M base x T w)
        (TrackedOutputShift.finalFrame M (project M (ChildCall.final M base x T w)) w) := by
  rw [← embed_project,run_embed]
  have h := TrackedOutputShift.shift_correct M (project M (ChildCall.final M base x T w)) w
  rw [← correct_handoff] at h
  exact congrArg (embed M (ChildCall.final M base x T w)) h

private theorem tagged_getD (M : MultitapeTM) (w : List M.Sym) (p : ℕ) :
    (w.map (fun a => some (a,true))).getD p (some (M.blank,false)) =
      some (w.getD p M.blank,decide (p < w.length)) := by
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getD_eq_getElem _ _ hp]
    simp [hp]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hp),List.getD_eq_default _ _ (Nat.le_of_not_gt hp)]
    simp [hp]

private theorem native_tape (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (w : List Bool) (hm : base 0 = none) :
    TrackedOutputShift.outputTape M base w = (program M).tapeOf (w.map (program M).bitSym) := by
  funext p
  cases p with
  | zero => exact hm
  | succ p =>
    have ht := tagged_getD M (w.map M.bitSym) p
    have he : (w.map M.bitSym).map (fun a => some (a,true)) = w.map (program M).bitSym := by
      rw [List.map_map]
      congr 1
      funext b
      cases b <;> rfl
    rw [List.length_map,he] at ht
    exact ht.symm

theorem final_output (M : MultitapeTM) (base : (preparation M).Cfg) (w : List Bool)
    (hm : base.cells (preparation M).outTape 0 = none) :
    (final M base w).cells (program M).outTape = (program M).tapeOf (w.map (program M).bitSym) := by
  exact native_tape M (base.cells (preparation M).outTape) w hm

end BitDFT.NativeChildOutput

open BitDFT.NativeChildOutput BitDFT IntMul MachineSequence

theorem solution (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 181*n*q+10*T ∧
      (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
        final M (ChildCall.final M
          (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w ∧
      (program M).HaltsWithOutput (requestedInput b U) [] t w ∧
      ((program M).step^[t] ((program M).initCfg (requestedInput b U) [])).head (program M).outTape = w.length+1 := by
  dsimp only
  let q := guardPrecision n b
  let x := fourierInput q U
  obtain ⟨s,v,hs,hr⟩ := BitDFT.child_call_correct M n b hn hb U T halt w out
  let ready := CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x
  let called := ChildCall.final M ready x T w
  have hhalt : ((preparation M).step^[s] ((preparation M).initCfg (requestedInput b U) [])).state =
      (native (preparation M)).exit := by
    rw [hr]
    rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (native (preparation M)) (control M)
    ((preparation M).initCfg (requestedInput b U) []) s (4*w.length+4) hhalt
  change (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
    rightCfg (native (preparation M)) (control M)
      ((machine M).step^[4*w.length+4] (handoff (native (preparation M)) (control M)
        ((preparation M).step^[s] ((preparation M).initCfg (requestedInput b U) [])))) at he
  rw [hr] at he
  change (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
    rightCfg (native (preparation M)) (control M)
      ((machine M).step^[4*w.length+4] (handoff (native (preparation M)) (control M) called)) at he
  have hc := shift_run M ready x T w
  rw [hc] at he
  have hmark : called.cells (preparation M).outTape 0 = none := by
    change (ChildCall.final M ready x T w).cells (ChildCall.program M).outTape 0 = none
    rw [returned_output]
    change ready.cells (ChildCall.preparation M).outTape 0 = none
    rfl
  refine ⟨t,v,?_,he,?_,?_⟩
  · have hw := BitDFT.output_length_le_time M (fourierInput (guardPrecision n b) U) [] w T ⟨halt,out⟩
    have hq : 1 ≤ guardPrecision n b := by unfold guardPrecision; omega
    have hp : 1 ≤ n*guardPrecision n b := by nlinarith
    nlinarith
  · constructor
    · rw [he]; rfl
    · rw [he]
      exact final_output M called w hmark
  · rw [he]
    rfl
