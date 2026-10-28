-- Prove2me | solution 1 for BitDFT.request_headers_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:11:15.941182+00:00
-- url     : https://prove2.me/submissions/3cc238f8-85f7-406c-9c71-314a8b96f261

import Definitions.Def_BitDFT_RequestHeaders
import Theorems.Thm_BitDFT_header_offsets_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_machine_sequence_bound

noncomputable section
namespace BitDFT.RequestHeaders
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem first_run (n rest : List Bool) :
    firstControl.machine.step^[2*n.length+3] (firstInitial (header n++rest)) =
      firstFinished (header n++rest) n := by
  change first.step^[_] _ = _
  unfold firstInitial firstFinished
  rw [BitDFT.tape_permutation_run,(BitDFT.tape_extension_correct reader 1).1]
  have h := BitDFT.header_offsets_correct [] n rest
  simp only [List.nil_append,List.length_nil] at h
  simpa [header,List.append_assoc] using congrArg
    (fun c => TapePermutation.embed second swap34 (by decide)
      (TapeExtension.embed reader 1 (fun _ => second.tapeOf []) (fun _ => 0) c)) h

theorem second_run (n b rest : List Bool) :
    second.step^[2*b.length+3] (secondInitial (header n++header b++rest) n) =
      secondFinished (header n++header b++rest) n b := by
  unfold secondInitial secondFinished
  rw [(BitDFT.tape_extension_correct reader 1).1]
  have h := BitDFT.header_offsets_correct (header n) b rest
  simpa [header,List.append_assoc] using congrArg
    (TapeExtension.embed reader 1 (fun _ => second.tapeOf (n.map second.bitSym)) (fun _ => n.length+1)) h

def resetInitial (x n : List Bool) : reset.machine.Cfg :=
  ⟨false,(firstFinished x n).cells,(firstFinished x n).head⟩
def resetFinished (x n : List Bool) : reset.machine.Cfg :=
  ⟨true,(secondInitial x n).cells,(secondInitial x n).head⟩

private theorem tape_no_start (w : List HeaderReader.machine.Sym)
    (hw : ∀ a ∈ w, a ≠ TapeCopy.Sym.start) (p : ℕ) (hp : 0 < p) :
    HeaderReader.machine.tapeOf w p ≠ TapeCopy.Sym.start := by
  cases p with
  | zero => omega
  | succ p =>
    simp only [MultitapeTM.tapeOf]
    by_cases h : p < w.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hw _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
      decide

theorem reset_run (x n : List Bool) :
    reset.machine.step (resetInitial x n) = resetFinished x n := by
  let c := resetInitial x n
  have h0 : c.head 0 = 2*n.length+2 := by
    simp [c,resetInitial,firstFinished,TapePermutation.embed,TapeExtension.embed,
      HeaderOffsets.finished,MachineSequence.stopCfg,HeaderOffsets.rawFinished,swap34,Equiv.swap_apply_def]
  have h1 : c.head 1 = 1 := by
    simp [c,resetInitial,firstFinished,TapePermutation.embed,TapeExtension.embed,
      HeaderOffsets.finished,MachineSequence.stopCfg,HeaderOffsets.rawFinished,swap34,Equiv.swap_apply_def]
  have hnot (i : Fin 5) (hi : i = 0 ∨ i = 1) : c.cells i (c.head i) ≠ TapeCopy.Sym.start := by
    rcases hi with rfl | rfl
    · have hm : ∀ a ∈ (x.map HeaderReader.machine.bitSym ++ [TapeCopy.Sym.sep]), a ≠ TapeCopy.Sym.start := by
        intro a ha
        simp only [List.mem_append,List.mem_map,List.mem_singleton] at ha
        rcases ha with ⟨b,hb,rfl⟩ | rfl
        · cases b <;> decide
        · decide
      rw [h0]
      simpa [c,resetInitial,firstFinished,TapePermutation.embed,TapeExtension.embed,
        HeaderOffsets.finished,MachineSequence.stopCfg,HeaderOffsets.rawFinished,swap34,Equiv.swap_apply_def,
        MultitapeTM.tapeOf,MultitapeTM.bitSym] using
        tape_no_start _ hm (2*n.length+2) (by omega)
    · simp [c,resetInitial,firstFinished,TapePermutation.embed,TapeExtension.embed,
        HeaderOffsets.finished,MachineSequence.stopCfg,HeaderOffsets.rawFinished,swap34,Equiv.swap_apply_def,
        MultitapeTM.tapeOf]
  have ht : resetTransition c.state (fun i => c.cells i (c.head i)) =
      (true,fun i => (c.cells i (c.head i),if i = 0 ∨ i = 1 then Move.left else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      change HeaderReader.protect (c.cells i (c.head i)) (c.cells i (c.head i),if i = 0 ∨ i = 1 then Move.left else Move.stay) = _
      by_cases hi : i = 0 ∨ i = 1
      · simp [HeaderReader.protect,hnot i hi,hi]
      · by_cases hm : c.cells i (c.head i) = TapeCopy.Sym.start <;> simp [HeaderReader.protect,hi,hm]
  change reset.machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,show reset.transition = resetTransition from rfl,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((resetTransition c.state _).2 i).1) = _
    rw [ht]
    simp only [Function.update_eq_self]
    funext i
    fin_cases i <;> simp [c,resetInitial,resetFinished,firstFinished,secondInitial,
      TapePermutation.embed,TapeExtension.embed,HeaderOffsets.prepared,HeaderOffsets.finished,
      MachineSequence.stopCfg,HeaderOffsets.rawPrepared,HeaderOffsets.rawFinished,swap34,Equiv.swap_apply_def] <;> rfl
  · simp only [MultitapeTM.step,show reset.transition = resetTransition from rfl,ht]
    funext i
    fin_cases i <;> simp [c,resetInitial,resetFinished,firstFinished,secondInitial,
      TapePermutation.embed,TapeExtension.embed,HeaderOffsets.prepared,HeaderOffsets.finished,
      MachineSequence.stopCfg,HeaderOffsets.rawPrepared,HeaderOffsets.rawFinished,swap34,Equiv.swap_apply_def,
      header,Nat.add_assoc,two_mul]

theorem init_correct (x : List Bool) :
    machine.initCfg x [] = leftCfg firstControl restControl (firstInitial x) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [MultitapeTM.initCfg,leftCfg,firstInitial,TapePermutation.embed,
      TapeExtension.embed,HeaderOffsets.prepared,HeaderOffsets.rawPrepared,stopCfg,
      swap34,Equiv.swap_apply_def,MultitapeTM.inTape] <;> rfl
  · funext i
    fin_cases i <;> simp [MultitapeTM.initCfg,leftCfg,firstInitial,TapePermutation.embed,
      TapeExtension.embed,HeaderOffsets.prepared,HeaderOffsets.rawPrepared,stopCfg,
      swap34,Equiv.swap_apply_def]

theorem headers_run (n b rest : List Bool) :
    ∃ t, t ≤ 2*n.length+2*b.length+9 ∧
      machine.step^[t] (machine.initCfg (header n++header b++rest) []) =
        final (header n++header b++rest) n b := by
  let x := header n++header b++rest
  have hr : (reset.machine.step^[1] (resetInitial x n)).state = reset.exit := by
    rw [Function.iterate_one,reset_run]; rfl
  obtain ⟨u,hu,he⟩ := BitDFT.machine_sequence_bound reset (native second)
    (resetInitial x n) 1 (2*b.length+3) hr
  rw [Function.iterate_one,reset_run] at he
  have hh : handoff reset (native second) (resetFinished x n) = secondInitial x n := rfl
  rw [hh] at he
  change restControl.machine.step^[u] (leftCfg reset (native second) (resetInitial x n)) =
    rightCfg reset (native second) (second.step^[2*b.length+3] (secondInitial x n)) at he
  rw [second_run] at he
  have hf : firstControl.machine.step^[2*n.length+3] (firstInitial x) = firstFinished x n := by
    simpa [x,List.append_assoc] using first_run n (header b++rest)
  have hfhalt : (firstControl.machine.step^[2*n.length+3] (firstInitial x)).state = firstControl.exit := by
    rw [hf]; rfl
  obtain ⟨t,ht,htRun⟩ := BitDFT.machine_sequence_bound firstControl restControl
    (firstInitial x) (2*n.length+3) u hfhalt
  rw [hf] at htRun
  have hentry : handoff firstControl restControl (firstFinished x n) =
      leftCfg reset (native second) (resetInitial x n) := rfl
  rw [hentry,he] at htRun
  refine ⟨t,by omega,?_⟩
  rw [init_correct]
  exact htRun

end BitDFT.RequestHeaders


open BitDFT.RequestHeaders IntMul

theorem solution (n b rest : List Bool) :
    ∃ t, t ≤ 2*n.length+2*b.length+9 ∧
      machine.step^[t] (machine.initCfg (header n++header b++rest) []) =
        final (header n++header b++rest) n b := by
  exact headers_run n b rest
