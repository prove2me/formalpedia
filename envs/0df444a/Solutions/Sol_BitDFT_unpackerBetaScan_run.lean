-- Prove2me | solution 1 for BitDFT.unpackerBetaScan_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T09:37:55.936397+00:00
-- url     : https://prove2.me/submissions/3e586bbc-f352-43c0-9edf-bd8deab0969e

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

theorem inT_eq : (inT : Fin 6) = machine.inTape := rfl

theorem step_some (q : Q) (cells : Fin machine.k → ℕ → machine.Sym)
    (head : Fin machine.k → ℕ) :
    machine.step ⟨some q, cells, head⟩ =
      ⟨some (spec q (fun i => cells i (head i))).1,
       fun i => Function.update (cells i) (head i) ((guard q (fun i => cells i (head i)) i)).1,
       fun i => mvH ((guard q (fun i => cells i (head i)) i)).2 (head i)⟩ := by
  delta machine
  rfl

theorem cntR_ne_inT : cntR ≠ inT := by decide
theorem cnt_ne_inT : cnt ≠ inT := by decide

/-- **The `betaUnary` transition rule, written out.**  On a unary mark the phase stays
`betaUnary`, the input head steps right, and the `β` counter tape receives a mark and steps
right. -/
theorem spec_betaUnary_mark (g κ s : Bool) (a : Fin 6 → Sym) (h : a inT = Sym.one) :
    (spec ⟨.betaUnary, g, κ, s⟩ a).1 = ⟨.betaUnary, g, κ, s⟩ ∧
    (spec ⟨.betaUnary, g, κ, s⟩ a).2 inT = (a inT, Move.right) ∧
    (spec ⟨.betaUnary, g, κ, s⟩ a).2 cnt = (Sym.one, Move.right) ∧
    ∀ i, i ≠ inT → i ≠ cnt → (spec ⟨.betaUnary, g, κ, s⟩ a).2 i = (a i, Move.stay) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [spec, h, if_true]
  · simp only [spec, h, if_true, if_pos rfl]
  · simp only [spec, h, if_true, cnt_ne_inT, if_false, if_pos rfl]
  · intro i hi1 hi2
    simp only [spec, h, if_true, hi1, hi2, if_false]

/-- On the input tape the guard passes the symbol and the phase's move through. -/
theorem guard_inT (q : Q) (a : Fin 6 → Sym) (h : a inT ≠ Sym.start) :
    (guard q a inT).1 = a inT ∧ (guard q a inT).2 = ((spec q a).2 inT).2 := by
  simp [guard, h]

/-- The input-side frame of the β-header scan: the phase is `rUnary`, the input tape is `ci` and its
head is `hi`.  The other tapes are deliberately absent: the phase rule reads only the symbol under
the input head, and the guard's input clause reads only that cell as well, so neither the scan's
progress nor its symbol depends on them. -/
def InFrame (c : machine.Cfg) (ci : ℕ → Sym) (hi : ℕ) : Prop :=
  c.state = some ⟨.betaUnary, false, false, false⟩ ∧
  c.cells machine.inTape = ci ∧ c.head machine.inTape = hi

/-- **One step of the mark scan.**  From the input-side frame, reading a mark, the machine stays in
`rUnary`, leaves the input tape's symbols alone and steps the input head right. -/
theorem scan_step (c : machine.Cfg) (ci : ℕ → Sym) (hi : ℕ)
    (hf : InFrame c ci hi) (hmark : ci hi = Sym.one) :
    InFrame (machine.step c) ci (hi + 1) := by
  obtain ⟨hst, hcin, hhin⟩ := hf
  rcases c with ⟨st, cl, hd⟩
  simp only at hst hcin hhin
  subst hst
  have hcin' : cl inT = ci := hcin
  have hhin' : hd inT = hi := hhin
  have hread : (fun i => cl i (hd i)) inT = Sym.one := by
    show cl inT (hd inT) = Sym.one
    rw [hcin', hhin']; exact hmark
  have hsp := spec_betaUnary_mark false false false (fun i => cl i (hd i)) hread
  have hs : (fun i => cl i (hd i)) inT ≠ Sym.start := by
    rw [hread]; exact (by decide : Sym.one ≠ Sym.start)
  have hg := guard_inT ⟨.betaUnary, false, false, false⟩ (fun i => cl i (hd i)) hs
  rw [step_some]
  refine ⟨congrArg some hsp.1, ?_, ?_⟩
  · show Function.update (cl machine.inTape) (hd machine.inTape)
      ((guard ⟨.betaUnary, false, false, false⟩ (fun i => cl i (hd i)) inT)).1 = ci
    have hval : (guard ⟨.betaUnary, false, false, false⟩ (fun i => cl i (hd i)) inT).1 = ci hi := by
      rw [hg.1]
      show cl inT (hd inT) = ci hi
      rw [hhin']
      exact congrFun hcin' hi
    rw [hval, hhin, hcin]
    exact Function.update_eq_self _ _
  · show mvH ((guard ⟨.betaUnary, false, false, false⟩ (fun i => cl i (hd i)) inT)).2
      (hd machine.inTape) = hi + 1
    rw [hg.2, hsp.2.1, hhin]
    rfl

/-- **The unary scan over `k` marks.**  Starting from the input-side frame with `k` marks ahead of
the head, after `k` transitions the machine is still in the phase, the input tape still carries `ci`,
and the head has advanced by exactly `k`. -/
theorem betaScan_run (k : ℕ) (c : machine.Cfg) (ci : ℕ → Sym) (hi : ℕ)
    (hf : InFrame c ci hi) (hm : ∀ j, j < k → ci (hi + j) = Sym.one) :
    InFrame (machine.step^[k] c) ci (hi + k) := by
  induction k generalizing c hi with
  | zero => simpa using hf
  | succ k ih =>
    have hframe : InFrame (machine.step^[k] c) ci (hi + k) :=
      ih c hi hf (fun j hj => hm j (by omega))
    have hmark : ci (hi + k) = Sym.one := hm k (by omega)
    rw [Function.iterate_succ_apply']
    exact scan_step _ ci (hi + k) hframe hmark

end BitDFT.Unpacker

theorem solution (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg) (ci : ℕ → TMKit.Sym) (hi : ℕ)
    (h1 : c.state = some ⟨BitDFT.Unpacker.Ph.betaUnary, false, false, false⟩)
    (h2 : c.cells BitDFT.Unpacker.machine.inTape = ci)
    (h3 : c.head BitDFT.Unpacker.machine.inTape = hi)
    (hm : ∀ j, j < k → ci (hi + j) = TMKit.Sym.one) :
    (BitDFT.Unpacker.machine.step^[k] c).state
        = some ⟨BitDFT.Unpacker.Ph.betaUnary, false, false, false⟩ ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells BitDFT.Unpacker.machine.inTape = ci ∧
      (BitDFT.Unpacker.machine.step^[k] c).head BitDFT.Unpacker.machine.inTape = hi + k :=
  BitDFT.Unpacker.betaScan_run k c ci hi ⟨h1, h2, h3⟩ hm
