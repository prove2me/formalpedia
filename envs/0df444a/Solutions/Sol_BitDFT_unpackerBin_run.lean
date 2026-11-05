-- Prove2me | solution 1 for BitDFT.unpackerBin_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:52:55.810347+00:00
-- url     : https://prove2.me/submissions/c2d4aa98-ca7d-4ab1-bc3a-4b0cdea0bf1f

import Mathlib
import Definitions.Def_BitDFT_unpackerMachineV4
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace BitDFT.Unpacker
open IntMul TMKit

def mvH (m : Move) (h : ℕ) : ℕ :=
  match m with
  | Move.left => h - 1
  | Move.stay => h
  | Move.right => h + 1

theorem step_some (q : Q) (cells : Fin machine.k → ℕ → machine.Sym)
    (head : Fin machine.k → ℕ) :
    machine.step ⟨some q, cells, head⟩ =
      ⟨some (spec q (fun i => cells i (head i))).1,
       fun i => Function.update (cells i) (head i) ((guard q (fun i => cells i (head i)) i)).1,
       fun i => mvH ((guard q (fun i => cells i (head i)) i)).2 (head i)⟩ := by
  delta machine
  rfl

/-- The `r`-counter tape. -/
def cntT : Fin machine.k := ⟨5, by delta machine; norm_num⟩

theorem inT_ne_cntR : inT ≠ cntR := by decide

/-- The countdown's rule on a mark. -/
theorem spec_rBinary_mark (g κ s : Bool) (a : Fin 6 → Sym) (h : a cntR = Sym.one) :
    (spec ⟨.rBinary, g, κ, s⟩ a).1 = ⟨.rBinary, g, κ, s⟩ ∧
    (spec ⟨.rBinary, g, κ, s⟩ a).2 cntR = (Sym.blank, Move.left) ∧
    (spec ⟨.rBinary, g, κ, s⟩ a).2 inT = (a inT, Move.right) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [spec, h, if_true]
  · simp only [spec, h, if_true, if_pos rfl]
  · simp only [spec, h, if_true, inT_ne_cntR, if_false, if_pos rfl]

/-- The guard leaves a cell alone whenever the cell is not the end marker, is not the input tape,
and the phase does not ask to write the end marker there. -/
theorem guard_off (q : Q) (a : Fin 6 → Sym) (i : Fin 6)
    (hne : a i ≠ Sym.start) (hni : i ≠ inT) (hw : ((spec q a).2 i).1 ≠ Sym.start) :
    guard q a i = (spec q a).2 i := by
  simp [guard, hne, hni, hw]

/-- On the input tape the guard passes the symbol and the phase's move through, provided the head
has left the end marker. -/
theorem guard_inT (q : Q) (a : Fin 6 → Sym) (h : a inT ≠ Sym.start) :
    (guard q a inT).1 = a inT ∧ (guard q a inT).2 = ((spec q a).2 inT).2 := by
  simp [guard, h]

/-- The two-tape frame of the countdown. -/
def BinFrame (c : machine.Cfg) (ci cc : ℕ → Sym) (hi hc : ℕ) : Prop :=
  c.state = some ⟨.rBinary, false, false, false⟩ ∧
  c.cells machine.inTape = ci ∧ c.head machine.inTape = hi ∧
  c.cells cntT = cc ∧ c.head cntT = hc

/-- **One step of the countdown.** -/
theorem bin_step (c : machine.Cfg) (ci cc : ℕ → Sym) (hi hc : ℕ)
    (hf : BinFrame c ci cc hi hc)
    (hmark : cc hc = Sym.one) (hin : ci hi ≠ Sym.start) :
    BinFrame (machine.step c) ci (Function.update cc hc Sym.blank) (hi + 1) (hc - 1) := by
  obtain ⟨hst, hcin, hhin, hccn, hhcn⟩ := hf
  rcases c with ⟨st, cl, hd⟩
  simp only at hst hcin hhin hccn hhcn
  subst hst
  have hcin' : cl inT = ci := hcin
  have hhin' : hd inT = hi := hhin
  have hccn' : cl cntT = cc := hccn
  have hhcn' : hd cntT = hc := hhcn
  have hread_cnt : (fun i => cl i (hd i)) cntR = Sym.one := by
    show cl cntT (hd cntT) = Sym.one
    rw [hccn', hhcn']; exact hmark
  have hread_in : (fun i => cl i (hd i)) inT ≠ Sym.start := by
    show cl inT (hd inT) ≠ Sym.start
    rw [hcin', hhin']; exact hin
  have hsp := spec_rBinary_mark false false false (fun i => cl i (hd i)) hread_cnt
  have hs : (fun i => cl i (hd i)) cntR ≠ Sym.start := by
    rw [hread_cnt]; exact (by decide : Sym.one ≠ Sym.start)
  have hne : cntR ≠ inT := Ne.symm inT_ne_cntR
  have hgc : (guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) cntR)
      = (spec ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i))).2 cntR := by
    apply guard_off
    · show (fun i => cl i (hd i)) cntR ≠ Sym.start
      rw [hread_cnt]; exact (by decide : Sym.one ≠ Sym.start)
    · exact Ne.symm inT_ne_cntR
    · rw [hsp.2.1]; exact (by decide : (Sym.blank : Sym) ≠ Sym.start)
  have hgi0 := guard_inT ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) hread_in
  have hg_in : (guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) inT).1
      = (fun i => cl i (hd i)) inT ∧
      (guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) inT).2 = Move.right := by
    refine ⟨hgi0.1, ?_⟩
    rw [hgi0.2, hsp.2.2]
  have hg_cnt : (guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) cntR).1
      = Sym.blank ∧
      (guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) cntR).2 = Move.left := by
    rw [hgc, hsp.2.1]
    exact ⟨rfl, rfl⟩
  rw [step_some]
  unfold BinFrame
  refine ⟨congrArg some hsp.1, ?_, ?_, ?_, ?_⟩
  · show Function.update (cl machine.inTape) (hd machine.inTape)
      ((guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) inT)).1 = ci
    have hv : (guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) inT).1 = ci hi := by
      rw [hg_in.1]
      show cl inT (hd inT) = ci hi
      rw [hhin']
      exact congrFun hcin' hi
    rw [hv, hhin, hcin]
    exact Function.update_eq_self _ _
  · show mvH ((guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) inT)).2
      (hd machine.inTape) = hi + 1
    rw [hg_in.2, hhin]; rfl
  · show Function.update (cl cntT) (hd cntT)
      ((guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) cntR)).1
      = Function.update cc hc Sym.blank
    rw [hg_cnt.1, hccn', hhcn']
    rfl
  · show mvH ((guard ⟨.rBinary, false, false, false⟩ (fun i => cl i (hd i)) cntR)).2
      (hd cntT) = hc - 1
    rw [hg_cnt.2, hhcn']
    rfl

/-- The counter tape after `k` countdown steps from head `hc`: the `k` cells from `hc-k+1` to `hc`
are blank. -/
def blanked (cc : ℕ → Sym) (hc k : ℕ) : ℕ → Sym :=
  fun p => if hc - k < p ∧ p ≤ hc then Sym.blank else cc p

theorem blanked_zero (cc : ℕ → Sym) (hc : ℕ) : blanked cc hc 0 = cc := by
  funext p
  simp only [blanked, Nat.sub_zero]
  rw [if_neg (by omega : ¬ (hc < p ∧ p ≤ hc))]

theorem blanked_push (cc : ℕ → Sym) (hc k : ℕ) (h1 : 1 ≤ hc - k) :
    Function.update (blanked cc hc k) (hc - k) Sym.blank = blanked cc hc (k + 1) := by
  funext p
  rw [Function.update_apply]
  simp only [blanked]
  by_cases hp : p = hc - k
  · subst hp
    rw [if_pos rfl, if_pos (by omega : hc - (k + 1) < hc - k ∧ hc - k ≤ hc)]
  · rw [if_neg hp]
    by_cases hq : hc - (k + 1) < p ∧ p ≤ hc
    · have hq' : hc - k < p ∧ p ≤ hc := ⟨by omega, hq.2⟩
      rw [if_pos hq', if_pos hq]
    · rw [if_neg (by omega : ¬ (hc - k < p ∧ p ≤ hc)), if_neg hq]

theorem blanked_mark (cc : ℕ → Sym) (hc k : ℕ) (h : cc (hc - k) = Sym.one) :
    blanked cc hc k (hc - k) = Sym.one := by
  simp only [blanked]
  rw [if_neg (by omega : ¬ (hc - k < hc - k ∧ hc - k ≤ hc)), h]

/-- **The countdown over `k` marks.** -/
theorem bin_run (k : ℕ) (c : machine.Cfg) (ci cc : ℕ → Sym) (hi hc : ℕ)
    (hf : BinFrame c ci cc hi hc) (hin : ∀ p, ci p ≠ Sym.start)
    (hk : k < hc) (hm : ∀ j, j < k → cc (hc - j) = Sym.one) :
    BinFrame (machine.step^[k] c) ci (blanked cc hc k) (hi + k) (hc - k) := by
  induction k generalizing c cc hc with
  | zero => simpa [blanked_zero] using hf
  | succ k ih =>
    have hf' : BinFrame (machine.step^[k] c) ci (blanked cc hc k) (hi + k) (hc - k) :=
      ih c cc hc hf (by omega) (fun j hj => hm j (by omega))
    have hm' : blanked cc hc k (hc - k) = Sym.one :=
      blanked_mark cc hc k (hm k (by omega))
    have hstep := bin_step (machine.step^[k] c) ci (blanked cc hc k) (hi + k) (hc - k)
      hf' hm' (hin (hi + k))
    rw [blanked_push cc hc k (by omega)] at hstep
    rw [show hc - k - 1 = hc - (k + 1) from by omega] at hstep
    rw [show hi + k + 1 = hi + (k + 1) from by omega] at hstep
    rw [Function.iterate_succ_apply']
    exact hstep


end BitDFT.Unpacker

theorem solution (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg) (ci cc : ℕ → TMKit.Sym)
    (hi hc : ℕ)
    (h1 : c.state = some ⟨BitDFT.Unpacker.Ph.rBinary, false, false, false⟩)
    (h2 : c.cells BitDFT.Unpacker.machine.inTape = ci)
    (h3 : c.head BitDFT.Unpacker.machine.inTape = hi)
    (h4 : c.cells (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ :
      Fin BitDFT.Unpacker.machine.k) = cc)
    (h5 : c.head (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ :
      Fin BitDFT.Unpacker.machine.k) = hc)
    (hin : ∀ p, ci p ≠ TMKit.Sym.start) (hk : k < hc)
    (hm : ∀ j, j < k → cc (hc - j) = TMKit.Sym.one) :
    (BitDFT.Unpacker.machine.step^[k] c).state
        = some ⟨BitDFT.Unpacker.Ph.rBinary, false, false, false⟩ ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells BitDFT.Unpacker.machine.inTape = ci ∧
      (BitDFT.Unpacker.machine.step^[k] c).head BitDFT.Unpacker.machine.inTape = hi + k ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells
          (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k)
        = (fun p => if hc - k < p ∧ p ≤ hc then TMKit.Sym.blank else cc p) ∧
      (BitDFT.Unpacker.machine.step^[k] c).head
          (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k)
        = hc - k :=
  BitDFT.Unpacker.bin_run k c ci cc hi hc ⟨h1, h2, h3, h4, h5⟩ hin hk hm

