-- Prove2me | solution 1 for BitDFT.unpackerSkip_stays
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:23:52.563581+00:00
-- url     : https://prove2.me/submissions/80902b56-fe21-4986-a28a-ab354a79e2af

import Mathlib
import Definitions.Def_BitDFT_unpackerMachineV2
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

theorem inT_ne_cntR : inT ≠ cntR := by decide

theorem step_some (q : Q) (cells : Fin machine.k → ℕ → machine.Sym)
    (head : Fin machine.k → ℕ) :
    machine.step ⟨some q, cells, head⟩ =
      ⟨some (spec q (fun i => cells i (head i))).1,
       fun i => Function.update (cells i) (head i) ((guard q (fun i => cells i (head i)) i)).1,
       fun i => mvH ((guard q (fun i => cells i (head i)) i)).2 (head i)⟩ := by
  delta machine
  rfl

/-- The `rSkipFalse` phase's rule keeps the phase. -/
theorem spec_rSkipFalse_stays (g κ s : Bool) (a : Fin 6 → Sym) :
    (spec ⟨.rSkipFalse, g, κ, s⟩ a).1 = ⟨.rSkipFalse, g, κ, s⟩ := rfl

/-- **The `rSkipFalse` phase never leaves itself.** -/
theorem rSkip_stays (k : ℕ) (c : machine.Cfg) (g κ s : Bool)
    (h : c.state = some ⟨.rSkipFalse, g, κ, s⟩) :
    (machine.step^[k] c).state = some ⟨.rSkipFalse, g, κ, s⟩ := by
  induction k generalizing c with
  | zero => simpa using h
  | succ k ih =>
    have hstep : (machine.step c).state = some ⟨.rSkipFalse, g, κ, s⟩ := by
      rcases c with ⟨st, cl, hd⟩
      simp only at h
      subst h
      rw [step_some]
      exact congrArg some (spec_rSkipFalse_stays g κ s (fun i => cl i (hd i)))
    rw [Function.iterate_succ]
    exact ih (machine.step c) hstep

/-- On a mark the `rBinary` phase erases it and steps the counter head left, while the input head
steps right. -/
theorem spec_rBinary_mark (g κ s : Bool) (a : Fin 6 → Sym) (h : a cntR = Sym.one) :
    (spec ⟨.rBinary, g, κ, s⟩ a).1 = ⟨.rBinary, g, κ, s⟩ ∧
    (spec ⟨.rBinary, g, κ, s⟩ a).2 cntR = (Sym.blank, Move.left) ∧
    (spec ⟨.rBinary, g, κ, s⟩ a).2 inT = (a inT, Move.right) ∧
    ∀ i, i ≠ cntR → i ≠ inT → (spec ⟨.rBinary, g, κ, s⟩ a).2 i = (a i, Move.stay) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [spec, h, if_true]
  · simp only [spec, h, if_true, if_pos rfl]
  · simp only [spec, h, if_true, inT_ne_cntR, if_false, if_pos rfl]
  · intro i hi1 hi2
    simp only [spec, h, if_true, hi1, hi2, if_false]

/-- **The `rBinary` exit rule.** -/
theorem spec_rBinary_stop (g κ s : Bool) (a : Fin 6 → Sym) (h : a cntR ≠ Sym.one) :
    (spec ⟨.rBinary, g, κ, s⟩ a).1 = ⟨.betaUnary, g, κ, s⟩ := by
  simp only [spec, h, if_false, go]

end BitDFT.Unpacker

theorem solution (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg) (g κ s : Bool)
    (h : c.state = some ⟨BitDFT.Unpacker.Ph.rSkipFalse, g, κ, s⟩) :
    (BitDFT.Unpacker.machine.step^[k] c).state
      = some ⟨BitDFT.Unpacker.Ph.rSkipFalse, g, κ, s⟩ :=
  BitDFT.Unpacker.rSkip_stays k c g κ s h
