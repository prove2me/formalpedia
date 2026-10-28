-- Prove2me | solution 1 for BitDFT.GroupedUnaryAdvance.correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T05:36:48.24972+00:00
-- url     : https://prove2.me/submissions/1cff1aab-163f-4223-a46e-d7ba24651569

import Definitions.Def_BitDFT_GroupedUnaryAdvance
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

theorem solution (N : MultitapeTM) (source counter : Fin N.k)
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
