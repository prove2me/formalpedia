-- Prove2me | solution 1 for BitDFT.low_operand_copy_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:11:30.74073+00:00
-- url     : https://prove2.me/submissions/3776d0ab-399b-44b9-b267-23a1ce2cb41b

import Definitions.Def_BitDFT_LowOperandCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic


namespace BitDFT.UnaryAdvance
open IntMul

private theorem cfg_ext {N : MultitapeTM} {source counter : Fin N.k}
    {hsc : source ≠ counter}
    (c d : (machine N source counter hsc).Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem run_continue (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (sourceHead counterHead : ℕ)
    (hone : base.cells counter counterHead = N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base false (sourceHead+1) (counterHead+1) := by
  cases base with
  | mk state cells head =>
    let c0 := frame N source counter hsc ⟨state, cells, head⟩ false sourceHead counterHead
    have hscanSimple : cells counter counterHead = N.one := by simpa using hone
    have hscan : cells counter
        (Function.update (Function.update head source sourceHead) counter counterHead counter) = N.one := by
      simp [Function.update, hsc, hscanSimple]
    apply cfg_ext
    · simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
    · funext i p
      by_cases hiS : i = source
      · subst i
        simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
      · by_cases hiC : i = counter
        · subst i
          simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
        · simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hiS, hiC]
    · funext i
      by_cases hiS : i = source
      · subst i
        simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
      · by_cases hiC : i = counter
        · subst i
          simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hsc]
        · simp [machine, control, MultitapeTM.step, transition, c0, frame, Function.update, hscan, hscanSimple, hiS, hiC]

private theorem run_stop (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (sourceHead counterHead : ℕ)
    (hstop : base.cells counter counterHead ≠ N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base true sourceHead counterHead := by
  cases base with
  | mk state cells head =>
    have hstop' : cells counter counterHead ≠ N.one := by simpa using hstop
    apply cfg_ext
    · simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hstop']
    · funext i p
      by_cases hiS : i = source
      · subst i
        simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hstop']
      · by_cases hiC : i = counter
        · subst i
          simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hstop']
        · simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hiS, hiC, hstop']
    · funext i
      by_cases hiS : i = source
      · subst i
        simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hstop']
      · by_cases hiC : i = counter
        · subst i
          simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hstop']
        · simp [machine, control, MultitapeTM.step, transition, frame, Function.update, hiS, hiC, hstop']

theorem correct (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (L sourceHead counterHead : ℕ)
    (hones : ∀ r, r < L → base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.one) :
    (machine N source counter hsc).step^[L+1]
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base true (sourceHead+L) (counterHead+L) := by
  induction L generalizing sourceHead counterHead with
  | zero =>
      have hs := run_stop N source counter hsc base sourceHead counterHead (by simpa using hstop)
      simpa using hs
  | succ L ih =>
      have hfirst := run_continue N source counter hsc base sourceHead counterHead
        (hones 0 (by omega))
      have htail : ∀ r, r < L → base.cells counter (counterHead+1+r) = N.one := by
        intro r hr
        have h := hones (r+1) (by omega)
        have heq : counterHead+1+r = counterHead+(r+1) := by omega
        rw [heq]
        exact h
      have hlast : base.cells counter (counterHead+1+L) ≠ N.one := by
        have heq : counterHead+1+L = counterHead+(L+1) := by omega
        rw [heq]
        exact hstop
      rw [show L+1+1 = (L+1)+1 by omega, Function.iterate_succ_apply]
      rw [hfirst]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (sourceHead+1) (counterHead+1) htail hlast

end BitDFT.UnaryAdvance


set_option autoImplicit false
open IntMul BitDFT.LowOperandCopy BitDFT.MachineSequence
open BitDFT.TapeExtension BitDFT.SuffixCopyTwoTape BitDFT.UnaryAdvance

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

theorem solution (h : sourceTape ≠ counterTape) (sign high : Bool) (bits : List Bool) :
    ∃ t : ℕ, t ≤ bits.length + 5 ∧
      (machine h).step^[t] (initial h sign high bits) = final h sign high bits := by
  let base := initialBase sign high bits
  let A : Controller storage := advance h
  let Q := copy
  let c0 := BitDFT.UnaryAdvance.frame storage sourceTape counterTape h base false 1 1
  have hone0 : base.cells counterTape 1 = storage.one := by
    change (storage.tapeOf [storage.one, storage.one]) 1 = storage.one
    simp [IntMul.MultitapeTM.tapeOf]
  have hone1 : base.cells counterTape (1+1) = storage.one := by
    change (storage.tapeOf [storage.one, storage.one]) 2 = storage.one
    simp [IntMul.MultitapeTM.tapeOf]
  have hstop : base.cells counterTape (1+2) ≠ storage.one := by
    change (storage.tapeOf [storage.one, storage.one]) 3 ≠ storage.one
    simp [IntMul.MultitapeTM.tapeOf, IntMul.MultitapeTM.blank, IntMul.MultitapeTM.one,
      storage, BitDFT.TapeExtension.machine, BitDFT.SuffixCopyTwoTape.machine]
  have hadvance := BitDFT.UnaryAdvance.correct storage sourceTape counterTape h base 2 1 1
    (by
      intro r hr
      interval_cases r
      · simpa using hone0
      · simpa [Nat.add_assoc] using hone1)
    hstop
  have hhalt : (A.machine.step^[3] c0).state = A.exit := by
    change ((BitDFT.UnaryAdvance.machine storage sourceTape counterTape h).step^[3]
      (BitDFT.UnaryAdvance.frame storage sourceTape counterTape h base false 1 1)).state = true
    rw [show 3 = 2+1 by omega, hadvance]
    rfl
  have hbit : storage.bitSym = (BitDFT.SuffixCopyTwoTape.machine).bitSym := by
    funext b
    cases b <;> rfl
  have hcopyStart : handoff A Q (A.machine.step^[3] c0) = copyStartBase sign high bits := by
    have hadvance' : A.machine.step^[3] c0 =
        BitDFT.UnaryAdvance.frame storage sourceTape counterTape h base true 3 3 := by
      simpa [A, advance, c0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadvance
    rw [hadvance']
    apply _root_.cfg_ext
    · simp [handoff, Q, copy, BitDFT.MachineSequence.native, copyStartBase, storage]
    · funext i p
      fin_cases i <;>
        simp [handoff, BitDFT.UnaryAdvance.frame, base, initialBase, copyStartBase,
          Function.update]
    · funext i
      fin_cases i <;>
        simp [handoff, BitDFT.UnaryAdvance.frame, base, initialBase, copyStartBase,
          sourceTape, counterTape, Function.update, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
  have hcopyStartEmbed : copyStartBase sign high bits =
      BitDFT.TapeExtension.embed BitDFT.SuffixCopyTwoTape.machine 1
        (fun i => if i.val < 2 then (BitDFT.SuffixCopyTwoTape.machine).tapeOf [] else
          storage.tapeOf [storage.one, storage.one])
        (fun i => if i.val = 2 then 3 else 0)
        (BitDFT.SuffixCopyTwoTape.frame ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .copy
          ([sign, high] ++ bits) [] 3) := by
    apply _root_.cfg_ext
    · simp [copyStartBase, storage, BitDFT.TapeExtension.embed,
        BitDFT.SuffixCopyTwoTape.frame, BitDFT.TapeExtension.machine,
        BitDFT.SuffixCopyTwoTape.machine]
    · funext i p
      fin_cases i <;> simp [copyStartBase, storage, IntMul.MultitapeTM.bitSym,
        IntMul.MultitapeTM.tapeOf, BitDFT.TapeExtension.embed,
        BitDFT.SuffixCopyTwoTape.frame, BitDFT.TapeExtension.machine,
        BitDFT.SuffixCopyTwoTape.machine, Function.update, hbit]
    · funext i
      fin_cases i <;> simp [copyStartBase, storage, IntMul.MultitapeTM.bitSym,
        IntMul.MultitapeTM.tapeOf, BitDFT.TapeExtension.embed,
        BitDFT.SuffixCopyTwoTape.frame, BitDFT.TapeExtension.machine,
        BitDFT.SuffixCopyTwoTape.machine, Function.update, hbit]
  have hfinalEmbed : finalBase sign high bits =
      BitDFT.TapeExtension.embed BitDFT.SuffixCopyTwoTape.machine 1
        (fun i => if i.val < 2 then (BitDFT.SuffixCopyTwoTape.machine).tapeOf [] else
          storage.tapeOf [storage.one, storage.one])
        (fun i => if i.val = 2 then 3 else 0)
        (BitDFT.SuffixCopyTwoTape.frame ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .halt
          ([sign, high] ++ bits) bits (2+(bits.length+1))) := by
    apply _root_.cfg_ext
    · simp [finalBase, storage, BitDFT.TapeExtension.embed,
        BitDFT.SuffixCopyTwoTape.frame, BitDFT.TapeExtension.machine,
        BitDFT.SuffixCopyTwoTape.machine]
    · funext i p
      fin_cases i <;> simp [finalBase, storage, IntMul.MultitapeTM.bitSym,
        IntMul.MultitapeTM.tapeOf, BitDFT.TapeExtension.embed,
        BitDFT.SuffixCopyTwoTape.frame, BitDFT.TapeExtension.machine,
        BitDFT.SuffixCopyTwoTape.machine, Function.update, hbit] <;> omega
    · funext i
      fin_cases i <;> simp [finalBase, storage, IntMul.MultitapeTM.bitSym,
        IntMul.MultitapeTM.tapeOf, BitDFT.TapeExtension.embed,
        BitDFT.SuffixCopyTwoTape.frame, BitDFT.TapeExtension.machine,
        BitDFT.SuffixCopyTwoTape.machine, Function.update, hbit] <;> omega
  have hcopyRun : Q.machine.step^[bits.length+1]
      (handoff A Q (A.machine.step^[3] c0)) = finalBase sign high bits := by
    have hRunEmbed := (BitDFT.tape_extension_correct BitDFT.SuffixCopyTwoTape.machine 1).1
      (fun i => if i.val < 2 then (BitDFT.SuffixCopyTwoTape.machine).tapeOf [] else
        storage.tapeOf [storage.one, storage.one])
      (fun i => if i.val = 2 then 3 else 0)
      (BitDFT.SuffixCopyTwoTape.frame ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .copy
        ([sign, high] ++ bits) [] 3) (bits.length+1)
    have hrunStorage : storage.step^[bits.length+1] (copyStartBase sign high bits) =
        finalBase sign high bits := by
      calc
        storage.step^[bits.length+1] (copyStartBase sign high bits) =
            storage.step^[bits.length+1]
              (BitDFT.TapeExtension.embed BitDFT.SuffixCopyTwoTape.machine 1
                (fun i => if i.val < 2 then (BitDFT.SuffixCopyTwoTape.machine).tapeOf [] else
                  storage.tapeOf [storage.one, storage.one])
                (fun i => if i.val = 2 then 3 else 0)
                (BitDFT.SuffixCopyTwoTape.frame
                  ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .copy
                  ([sign, high] ++ bits) [] 3)) := by rw [hcopyStartEmbed]
        _ = BitDFT.TapeExtension.embed BitDFT.SuffixCopyTwoTape.machine 1
              (fun i => if i.val < 2 then (BitDFT.SuffixCopyTwoTape.machine).tapeOf [] else
                storage.tapeOf [storage.one, storage.one])
              (fun i => if i.val = 2 then 3 else 0)
              (BitDFT.SuffixCopyTwoTape.machine.step^[bits.length+1]
                (BitDFT.SuffixCopyTwoTape.frame
                  ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .copy
                  ([sign, high] ++ bits) [] 3)) := hRunEmbed
        _ = finalBase sign high bits := by
          have hcopy := BitDFT.two_tape_suffix_copy_correct
            ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) [sign, high] bits []
          have hcopy' : (BitDFT.SuffixCopyTwoTape.machine).step^[bits.length+1]
              (BitDFT.SuffixCopyTwoTape.frame
                ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .copy
                ([sign, high] ++ bits) [] 3) =
              BitDFT.SuffixCopyTwoTape.frame
                ((BitDFT.SuffixCopyTwoTape.machine).initCfg [] []) .halt
                ([sign, high] ++ bits) bits (2+(bits.length+1)) := by
            simpa [Nat.add_assoc] using hcopy
          have hcopy'' := congrArg
            (fun c => BitDFT.TapeExtension.embed BitDFT.SuffixCopyTwoTape.machine 1
              (fun i => if i.val < 2 then (BitDFT.SuffixCopyTwoTape.machine).tapeOf [] else
                storage.tapeOf [storage.one, storage.one])
              (fun i => if i.val = 2 then 3 else 0) c) hcopy'
          exact hcopy''.trans hfinalEmbed.symm
    rw [hcopyStart]
    simpa [Q, copy, BitDFT.MachineSequence.native] using hrunStorage
  obtain ⟨v, hv, hrun⟩ := BitDFT.machine_sequence_bound A Q c0 3
    (bits.length+1) hhalt
  refine ⟨v, ?_, ?_⟩
  · omega
  · rw [hcopyRun] at hrun
    simpa [initial, final, base, A, advance, Q, copy, c0,
      BitDFT.LowOperandCopy.machine] using hrun
