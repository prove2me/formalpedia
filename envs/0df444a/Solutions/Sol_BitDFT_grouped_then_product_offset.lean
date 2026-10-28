-- Prove2me | solution 1 for BitDFT.grouped_then_product_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T05:53:10.751696+00:00
-- url     : https://prove2.me/submissions/81593404-22bf-4128-95b6-160e6bc262db

import Definitions.Def_BitDFT_GroupedUnaryAdvance
import Definitions.Def_BitDFT_LiftController
import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_BitAdvance
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_BitAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
import Mathlib.Tactic
open IntMul BitDFT.GroupedUnaryAdvance

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem group_step (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (j : Fin 3) (sourceHead counterHead : ℕ)
    (hj : j.val < 3) (hone : base.cells counter counterHead = N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base (.group j) sourceHead counterHead) =
      frame N source counter hsc base
        (if h : j.val = 2 then .group 0 else .group ⟨j.val+1, by have hj' := j.isLt; omega⟩)
        (if j.val = 2 then sourceHead+1 else sourceHead) (counterHead+1) := by
  cases base with
  | mk state cells head =>
    have hone' : cells counter counterHead = N.one := by simpa using hone
    have hscanSimple : cells counter counterHead = N.one := hone'
    have hcs : counter ≠ source := Ne.symm hsc
    have hread : cells counter
        (if counter = counter then counterHead else if counter = source then sourceHead else head counter) = N.one := by
      simp [hsc, hcs, hscanSimple]
    have hscan : cells counter
        (Function.update (Function.update head source sourceHead) counter counterHead counter) = N.one := by
      simp [Function.update, hsc, hscanSimple]
    by_cases hj2 : j.val = 2
    · apply cfg_ext
      · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
          transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2]
      · funext i p
        by_cases hiS : i = source
        · subst i
          simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2]
        · by_cases hiC : i = counter
          · subst i
            simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2]
          · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hiS, hiC, hj, hj2]
      · funext i
        by_cases hiS : i = source
        · subst i
          simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2]
        · by_cases hiC : i = counter
          · subst i
            simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2]
          · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hiS, hiC, hj, hj2]
    · have hj1 : j.val < 2 := by omega
      apply cfg_ext
      · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
          transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2, hj1]
      · funext i p
        by_cases hiS : i = source
        · subst i
          simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2, hj1]
        · by_cases hiC : i = counter
          · subst i
            simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hj, hj2, hj1]
          · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscan, hscanSimple, hsc, hcs, hiS, hiC, hj, hj2, hj1]
      · funext i
        by_cases hiS : i = source
        · subst i
          simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hscanSimple, hsc, hcs, hj, hj2, hj1]
        · by_cases hiC : i = counter
          · subst i
            simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscanSimple, hsc, hcs, hj, hj2, hj1]
          · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hscanSimple, hsc, hcs, hiS, hiC, hj, hj2, hj1]

theorem group0_stop (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (sourceHead counterHead : ℕ)
    (hstop : base.cells counter counterHead ≠ N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base (.group 0) sourceHead counterHead) =
      frame N source counter hsc base .halt (sourceHead+1) counterHead := by
  cases base with
  | mk state cells head =>
    have hstop' : cells counter counterHead ≠ N.one := by simpa using hstop
    have hcs : counter ≠ source := Ne.symm hsc
    apply cfg_ext
    · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
        transition, emit, frame, Function.update, hsc, hcs, hstop']
    · funext i p
      by_cases hiS : i = source
      · subst i
        simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
          transition, emit, frame, Function.update, hsc, hcs, hstop']
      · by_cases hiC : i = counter
        · subst i
          simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hsc, hcs, hstop']
        · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hsc, hcs, hiS, hiC, hstop']
    · funext i
      by_cases hiS : i = source
      · subst i
        simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
          transition, emit, frame, Function.update, hsc, hcs, hstop']
      · by_cases hiC : i = counter
        · subst i
          simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hsc, hcs, hstop']
        · simp [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hsc, hcs, hiS, hiC, hstop']

theorem group_run (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (r sourceHead counterHead : ℕ)
    (hones : ∀ j, j < 3*r → base.cells counter (counterHead+j) = N.one)
    (hstop : base.cells counter (counterHead+3*r) ≠ N.one) :
    (machine N source counter hsc).step^[3*r+1]
        (frame N source counter hsc base (.group 0) sourceHead counterHead) =
      frame N source counter hsc base .halt (sourceHead+r+1) (counterHead+3*r) := by
  induction r generalizing sourceHead counterHead with
  | zero =>
      have hs := group0_stop N source counter hsc base sourceHead counterHead (by simpa using hstop)
      simpa using hs
  | succ r ih =>
      have h0 := group_step N source counter hsc base ⟨0, by decide⟩ sourceHead counterHead
        (by decide) (hones 0 (by omega))
      have h1 := group_step N source counter hsc base ⟨1, by decide⟩ sourceHead (counterHead+1)
        (by decide) (hones 1 (by omega))
      have h2 := group_step N source counter hsc base ⟨2, by decide⟩ sourceHead (counterHead+2)
        (by decide) (hones 2 (by omega))
      have h0' : (machine N source counter hsc).step
          (frame N source counter hsc base (.group 0) sourceHead counterHead) =
          frame N source counter hsc base (.group 1) sourceHead (counterHead+1) := by
        simpa using h0
      have h1' : (machine N source counter hsc).step
          (frame N source counter hsc base (.group 1) sourceHead (counterHead+1)) =
          frame N source counter hsc base (.group 2) sourceHead (counterHead+2) := by
        simpa using h1
      have h2' : (machine N source counter hsc).step
          (frame N source counter hsc base (.group 2) sourceHead (counterHead+2)) =
          frame N source counter hsc base (.group 0) (sourceHead+1) (counterHead+3) := by
        simpa using h2
      have hcycle : (machine N source counter hsc).step^[3]
          (frame N source counter hsc base (.group 0) sourceHead counterHead) =
          frame N source counter hsc base (.group 0) (sourceHead+1) (counterHead+3) := by
        change (machine N source counter hsc).step^[2+1] _ = _
        rw [Function.iterate_succ_apply, h0']
        change (machine N source counter hsc).step^[1+1] _ = _
        rw [Function.iterate_succ_apply, h1']
        simpa using h2' 
      have htail : ∀ j, j < 3*r → base.cells counter (counterHead+3+j) = N.one := by
        intro j hj
        have h := hones (j+3) (by omega)
        have heq : counterHead+3+j = counterHead+(j+3) := by omega
        rw [heq]
        exact h
      have hlast : base.cells counter (counterHead+3+3*r) ≠ N.one := by
        have heq : counterHead+3+3*r = counterHead+3*(r+1) := by omega
        rw [heq]
        exact hstop
      rw [show 3*(r+1)+1 = (3*r+1)+3 by omega, Function.iterate_add_apply, hcycle]
      have hind := ih (sourceHead+1) (counterHead+3) htail hlast
      simpa [frame, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hind

theorem skip_step (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (j : Fin 5) (sourceHead counterHead : ℕ)
    (hone : base.cells counter counterHead = N.one) :
    (machine N source counter hsc).step
        (frame N source counter hsc base (.skip j) sourceHead counterHead) =
      frame N source counter hsc base
        (if h : j.val = 4 then .group 0 else .skip ⟨j.val+1, by have hj := j.isLt; omega⟩)
        sourceHead (counterHead+1) := by
  cases base with
  | mk state cells head =>
    have hone' : cells counter counterHead = N.one := by simpa using hone
    have hcs : counter ≠ source := Ne.symm hsc
    have hread : cells counter
        (if counter = counter then counterHead else if counter = source then sourceHead else head counter) = N.one := by
      simp [hsc, hcs, hone']
    by_cases hj4 : j.val = 4
    · apply cfg_ext
      · simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
          transition, emit, frame, Function.update, hread, hsc, hcs, hj4]
      · funext i p
        by_cases hiS : i = source
        · subst i
          simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hsc, hcs, hj4]
        · by_cases hiC : i = counter
          · subst i
            simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hsc, hcs, hj4]
          · simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hiS, hiC, hsc, hcs, hj4]
      · funext i
        by_cases hiS : i = source
        · subst i
          simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hsc, hcs, hj4]
        · by_cases hiC : i = counter
          · subst i
            simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hsc, hcs, hj4]
          · simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hiS, hiC, hsc, hcs, hj4]
    · have hj4' : j.val < 4 := by omega
      apply cfg_ext
      · simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
          transition, emit, frame, Function.update, hread, hsc, hcs, hj4, hj4']
      · funext i p
        by_cases hiS : i = source
        · subst i
          simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hsc, hcs, hj4, hj4']
        · by_cases hiC : i = counter
          · subst i
            simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hsc, hcs, hj4, hj4']
          · simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hiS, hiC, hsc, hcs, hj4, hj4']
      · funext i
        by_cases hiS : i = source
        · subst i
          simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
            transition, emit, frame, Function.update, hread, hsc, hcs, hj4, hj4']
        · by_cases hiC : i = counter
          · subst i
            simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hsc, hcs, hj4, hj4']
          · simp_all [machine, BitDFT.GroupedUnaryAdvance.control, MultitapeTM.step,
              transition, emit, frame, Function.update, hread, hiS, hiC, hsc, hcs, hj4, hj4']

theorem skip_five (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (sourceHead counterHead : ℕ)
    (hones : ∀ j, j < 5 → base.cells counter (counterHead+j) = N.one) :
    (machine N source counter hsc).step^[5]
      (frame N source counter hsc base (.skip 0) sourceHead counterHead) =
      frame N source counter hsc base (.group 0) sourceHead (counterHead+5) := by
  have h0 := skip_step N source counter hsc base ⟨0, by decide⟩ sourceHead counterHead (hones 0 (by omega))
  have h1 := skip_step N source counter hsc base ⟨1, by decide⟩ sourceHead (counterHead+1) (hones 1 (by omega))
  have h2 := skip_step N source counter hsc base ⟨2, by decide⟩ sourceHead (counterHead+2) (hones 2 (by omega))
  have h3 := skip_step N source counter hsc base ⟨3, by decide⟩ sourceHead (counterHead+3) (hones 3 (by omega))
  have h4 := skip_step N source counter hsc base ⟨4, by decide⟩ sourceHead (counterHead+4) (hones 4 (by omega))
  have h0' : (machine N source counter hsc).step
      (frame N source counter hsc base (.skip 0) sourceHead counterHead) =
      frame N source counter hsc base (.skip 1) sourceHead (counterHead+1) := by simpa using h0
  have h1' : (machine N source counter hsc).step
      (frame N source counter hsc base (.skip 1) sourceHead (counterHead+1)) =
      frame N source counter hsc base (.skip 2) sourceHead (counterHead+2) := by simpa using h1
  have h2' : (machine N source counter hsc).step
      (frame N source counter hsc base (.skip 2) sourceHead (counterHead+2)) =
      frame N source counter hsc base (.skip 3) sourceHead (counterHead+3) := by simpa using h2
  have h3' : (machine N source counter hsc).step
      (frame N source counter hsc base (.skip 3) sourceHead (counterHead+3)) =
      frame N source counter hsc base (.skip 4) sourceHead (counterHead+4) := by simpa using h3
  have h4' : (machine N source counter hsc).step
      (frame N source counter hsc base (.skip 4) sourceHead (counterHead+4)) =
      frame N source counter hsc base (.group 0) sourceHead (counterHead+5) := by simpa using h4
  change (machine N source counter hsc).step^[4+1] _ = _
  rw [Function.iterate_succ_apply, h0']
  change (machine N source counter hsc).step^[3+1] _ = _
  rw [Function.iterate_succ_apply, h1']
  change (machine N source counter hsc).step^[2+1] _ = _
  rw [Function.iterate_succ_apply, h2']
  change (machine N source counter hsc).step^[1+1] _ = _
  rw [Function.iterate_succ_apply, h3']
  rw [Function.iterate_succ_apply, h4']
  rfl

theorem grouped_unary_advance_correct (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (r sourceHead counterHead : ℕ)
    (hones : ∀ j, j < 3*r+5 → base.cells counter (counterHead+j) = N.one)
    (hstop : base.cells counter (counterHead+3*r+5) ≠ N.one) :
    (machine N source counter hsc).step^[3*r+6]
      (frame N source counter hsc base (.skip 0) sourceHead counterHead) =
      frame N source counter hsc base .halt (sourceHead+r+1) (counterHead+3*r+5) := by
  have hskip := skip_five N source counter hsc base sourceHead counterHead
    (fun j hj => hones j (by omega))
  have hgroupOnes : ∀ j, j < 3*r → base.cells counter (counterHead+5+j) = N.one := by
    intro j hj
    have h := hones (j+5) (by omega)
    have heq : counterHead+5+j = counterHead+(j+5) := by omega
    rw [heq]
    exact h
  have hgroupStop : base.cells counter (counterHead+5+3*r) ≠ N.one := by
    have heq : counterHead+5+3*r = counterHead+3*r+5 := by omega
    rw [heq]
    exact hstop
  rw [show 3*r+6 = (3*r+1)+5 by omega, Function.iterate_add_apply, hskip]
  have hgroup := group_run N source counter hsc base r sourceHead (counterHead+5)
    hgroupOnes hgroupStop
  simpa [frame, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgroup


set_option autoImplicit false
open IntMul BitDFT BitDFT.MachineSequence

private theorem cfg_ext₃ {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem rewind_then_bit_advance_to_offset_local
    (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (p L counterHead : ℕ)
    (hcounter : base.head counter = counterHead)
    (hmarker : base.cells source 0 = N.startSym)
    (hsource : ∀ r, 0 < r → base.cells source r ≠ N.startSym)
    (hbits : ∀ r, r < L →
      base.cells counter (counterHead+r) = N.zero ∨ base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.zero ∧
      base.cells counter (counterHead+L) ≠ N.one) :
    ∃ t : ℕ, t ≤ p + L + 3 ∧
      (MachineSequence.sequence (BitDFT.RewindTape.control N source)
        (BitDFT.BitAdvance.control N source counter hsc)).machine.step^[t]
        (MachineSequence.leftCfg (BitDFT.RewindTape.control N source)
          (BitDFT.BitAdvance.control N source counter hsc)
          (BitDFT.RewindTape.frame N source base false p)) =
      MachineSequence.rightCfg (BitDFT.RewindTape.control N source)
        (BitDFT.BitAdvance.control N source counter hsc)
        (BitDFT.BitAdvance.frame N source counter hsc base true (L+1)
          (counterHead+L)) := by
  let P := BitDFT.RewindTape.control N source
  let Q := BitDFT.BitAdvance.control N source counter hsc
  let c₀ := BitDFT.RewindTape.frame N source base false p
  have hrew := BitDFT.rewind_tape_correct N source base hmarker hsource p
  have hhalt : (P.machine.step^[p+1] c₀).state = P.exit := by
    rw [hrew]
    rfl
  obtain ⟨t, ht, hseq⟩ := BitDFT.machine_sequence_bound P Q c₀ (p+1) (L+1) hhalt
  have hhandoff : MachineSequence.handoff P Q
      (BitDFT.RewindTape.frame N source base true 1) =
      BitDFT.BitAdvance.frame N source counter hsc base false 1 counterHead := by
    apply cfg_ext₃
    · rfl
    · rfl
    · funext i
      by_cases hi : i = counter
      · subst i
        have hci : counter ≠ source := Ne.symm hsc
        simp [MachineSequence.handoff, BitDFT.RewindTape.frame,
          BitDFT.BitAdvance.frame, Function.update, hci, hcounter]
      · simp [MachineSequence.handoff, BitDFT.RewindTape.frame,
          BitDFT.BitAdvance.frame, Function.update, hi, hcounter]
  have hadv := BitDFT.BitAdvance.correct N source counter hsc base L 1
    counterHead hbits hstop
  rw [hrew, hhandoff, hadv] at hseq
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa [P, Q, c₀, Nat.add_comm] using hseq

open IntMul BitDFT.MachineSequence


private theorem cfg_ext₂ {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem solution
    (N : MultitapeTM)
    (unary operand product : Fin N.k)
    (huo : operand ≠ unary) (hup : unary ≠ product) (hop : operand ≠ product)
    (base : N.Cfg) (r operandHead p L : ℕ)
    (hoperandhead : base.head operand = operandHead)
    (hproducthead : base.head product = p)
    (hmarkerU : base.cells unary 0 = N.startSym)
    (hsourceU : ∀ j, 0 < j → base.cells unary j ≠ N.startSym)
    (hmarks : ∀ j, j < 3*r+5 → base.cells unary (1+j) = N.one)
    (hmarkStop : base.cells unary (1+3*r+5) ≠ N.one)
    (hmarkerP : base.cells product 0 = N.startSym)
    (hsourceP : ∀ j, 0 < j → base.cells product j ≠ N.startSym)
    (hbits : ∀ j, j < L →
      base.cells operand (operandHead+r+1+j) = N.zero ∨
      base.cells operand (operandHead+r+1+j) = N.one)
    (hbitStop : base.cells operand (operandHead+r+1+L) ≠ N.zero ∧
      base.cells operand (operandHead+r+1+L) ≠ N.one) :
    let P := BitDFT.RewindTape.control N unary
    let Q := BitDFT.GroupedUnaryAdvance.control N operand unary huo
    let S := BitDFT.MachineSequence.sequence P Q
    let c₀ := BitDFT.RewindTape.frame N unary base false (3*r+5)
    let cS : S.machine.Cfg := rightCfg P Q
      (BitDFT.GroupedUnaryAdvance.frame N operand unary huo base .halt
        (operandHead+r+1) (1+3*r+5))
    let R := BitDFT.RewindTape.control S.machine product
    let U := BitDFT.BitAdvance.control S.machine product operand (Ne.symm hop)
    let V := BitDFT.MachineSequence.sequence R U
  let Vflat := BitDFT.MachineSequence.liftController S V
    let Vflat := BitDFT.MachineSequence.liftController S V
    ∃ t ≤ (6*r+14)+(p+L+3)+1,
      (BitDFT.MachineSequence.sequence S Vflat).machine.step^[t]
        (leftCfg S Vflat (leftCfg P Q c₀)) =
      rightCfg S Vflat
        (rightCfg R U
          (BitDFT.BitAdvance.frame S.machine product operand (Ne.symm hop)
            cS true (L+1) (operandHead+r+1+L))) := by
  let P := BitDFT.RewindTape.control N unary
  let Q := BitDFT.GroupedUnaryAdvance.control N operand unary huo
  let S := BitDFT.MachineSequence.sequence P Q
  let c₀ := BitDFT.RewindTape.frame N unary base false (3*r+5)
  have hrewU := BitDFT.rewind_tape_correct N unary base hmarkerU hsourceU (3*r+5)
  have hhaltP : (P.machine.step^[(3*r+5)+1] c₀).state = P.exit := by rw [hrewU]; rfl
  obtain ⟨tS, htS, hseqS⟩ := BitDFT.machine_sequence_bound P Q c₀
    ((3*r+5)+1) (3*r+6) hhaltP
  have hhandoffS : handoff P Q (BitDFT.RewindTape.frame N unary base true 1) =
      BitDFT.GroupedUnaryAdvance.frame N operand unary huo base (.skip 0) operandHead 1 := by
    apply cfg_ext₂
    · rfl
    · rfl
    · funext i
      by_cases hiO : i = operand
      · subst i
        simp [handoff, BitDFT.RewindTape.frame, BitDFT.GroupedUnaryAdvance.frame,
          Function.update, hoperandhead, huo]
      · by_cases hiU : i = unary
        · subst i
          simp [handoff, BitDFT.RewindTape.frame, BitDFT.GroupedUnaryAdvance.frame,
            Function.update, huo, hoperandhead]
        · simp [handoff, BitDFT.RewindTape.frame, BitDFT.GroupedUnaryAdvance.frame,
            Function.update, hiO, hiU, huo]
  have hrunQ := grouped_unary_advance_correct N operand unary huo base r operandHead 1 hmarks hmarkStop
  rw [hrewU, hhandoffS, hrunQ] at hseqS
  let cS : S.machine.Cfg := rightCfg P Q
    (BitDFT.GroupedUnaryAdvance.frame N operand unary huo base .halt
      (operandHead+r+1) (1+3*r+5))
  have hhaltS : (S.machine.step^[tS] (BitDFT.MachineSequence.leftCfg P Q c₀)).state = S.exit := by
    rw [hseqS]
    rfl
  have hprodHead : cS.head product = p := by
    simp [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
      Function.update, hop, hup, Ne.symm hop, Ne.symm hup, hproducthead]
  have hcountHead : cS.head operand = operandHead+r+1 := by
    simp [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
      Function.update, huo, hoperandhead]
  have hprodMarker : cS.cells product 0 = S.machine.startSym := by
    simpa [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
      huo, hup] using hmarkerP
  have hprodSource : ∀ j, 0 < j → cS.cells product j ≠ S.machine.startSym := by
    intro j hj
    simpa [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
      huo, hup] using hsourceP j hj
  have hcounterBits : ∀ j, j < L →
      cS.cells operand (operandHead+r+1+j) = S.machine.zero ∨
      cS.cells operand (operandHead+r+1+j) = S.machine.one := by
    intro j hj
    simpa [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
      huo, hup] using hbits j hj
  have hcounterStop : cS.cells operand (operandHead+r+1+L) ≠ S.machine.zero ∧
      cS.cells operand (operandHead+r+1+L) ≠ S.machine.one := by
    constructor
    · simpa [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
        huo, hup] using hbitStop.1
    · simpa [cS, S, rightCfg, BitDFT.GroupedUnaryAdvance.frame,
        huo, hup] using hbitStop.2
  let R := BitDFT.RewindTape.control S.machine product
  let U := BitDFT.BitAdvance.control S.machine product operand (Ne.symm hop)
  let V := BitDFT.MachineSequence.sequence R U
  let Vflat := BitDFT.MachineSequence.liftController S V
  let cR := BitDFT.RewindTape.frame S.machine product cS false p
  have hrewP := BitDFT.rewind_tape_correct S.machine product cS hprodMarker hprodSource p
  have hhaltR : (R.machine.step^[p+1] cR).state = R.exit := by rw [hrewP]; rfl
  obtain ⟨tV, htV, hseqV⟩ := BitDFT.machine_sequence_bound R U cR (p+1) (L+1) hhaltR
  obtain ⟨u, hu, hrunV⟩ := rewind_then_bit_advance_to_offset_local S.machine product operand (Ne.symm hop)
    cS p L (operandHead+r+1) hcountHead hprodMarker hprodSource hcounterBits hcounterStop
  have hhandoffV : handoff S Vflat cS = BitDFT.MachineSequence.leftCfg R U cR := by
    apply cfg_ext₂
    · rfl
    · rfl
    · funext i
      by_cases hi : i = product
      · subst i
        simp [handoff, leftCfg, cR, V, R, U, BitDFT.RewindTape.frame, Function.update, hprodHead]
      · simp [handoff, leftCfg, cR, V, R, U, BitDFT.RewindTape.frame, Function.update, hi]
  have hseqSExact : S.machine.step^[tS] (BitDFT.MachineSequence.leftCfg P Q c₀) = cS := by
    simpa [cS] using hseqS
  obtain ⟨t, ht, houter⟩ := BitDFT.machine_sequence_bound S Vflat
    (BitDFT.MachineSequence.leftCfg P Q c₀) tS u hhaltS
  rw [hseqSExact, hhandoffV] at houter
  have hrunVflat : Vflat.machine.step^[u] (leftCfg R U cR) =
      rightCfg R U (BitDFT.BitAdvance.frame S.machine product operand (Ne.symm hop)
        cS true (L+1) (operandHead+r+1+L)) := by
    simpa [Vflat, BitDFT.MachineSequence.liftController] using hrunV
  rw [hrunVflat] at houter
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa [P, Q, S, V, Vflat, R, U, c₀, cS, BitDFT.MachineSequence.liftController] using houter
