-- Prove2me | solution 1 for BitDFT.unpackerSpec_rBinary_mark
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:01:45.303737+00:00
-- url     : https://prove2.me/submissions/16c9a413-e5d4-4204-976e-9b46ec201bc2

import Mathlib
import Definitions.Def_BitDFT_unpackerMachineV3
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

/-- The counter tape of the machine. -/
def cntT : Fin machine.k := ⟨5, by delta machine; norm_num⟩

theorem inT_ne_cntT : machine.inTape ≠ cntT := by
  intro h
  have h1 : (machine.inTape : Fin machine.k).val = 0 := rfl
  have h2 : (cntT : Fin machine.k).val = 5 := rfl
  rw [h] at h1; omega

theorem cntT_ne_inT : cntT ≠ machine.inTape := Ne.symm inT_ne_cntT

theorem inT_eq : (inT : Fin 6) = machine.inTape := rfl
theorem cntR_eq : (cntR : Fin 6) = cntT := rfl

theorem keepSym_of_ne (x : Sym) (h : x ≠ Sym.start) : keepSym x = x := by
  simp [keepSym, h]

/-- **The `rBinary` rule on a mark.** -/
theorem inT_ne_cntR : inT ≠ cntR := by decide

theorem spec_rBinary_mark (g κ s : Bool) (a : Fin 6 → Sym) (h : a cntR = Sym.one) :
    (spec ⟨.rBinary, g, κ, s⟩ a).1 = ⟨.rBinary, g, κ, s⟩ ∧
    (spec ⟨.rBinary, g, κ, s⟩ a).2 cntR = (Sym.blank, Move.left) ∧
    (spec ⟨.rBinary, g, κ, s⟩ a).2 inT = (a inT, Move.right) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [spec, h, if_true]
  · simp only [spec, h, if_true, if_pos rfl]
  · simp only [spec, h, if_true, inT_ne_cntR, if_false, if_pos rfl]

/-- **The `rBinary` exit rule.** -/
theorem spec_rBinary_stop (g κ s : Bool) (a : Fin 6 → Sym) (h : a cntR ≠ Sym.one) :
    (spec ⟨.rBinary, g, κ, s⟩ a).1 = ⟨.betaUnary, g, κ, s⟩ := by
  simp only [spec, h, if_false, go]

end BitDFT.Unpacker

theorem solution (g κ s : Bool) (a : Fin 6 → TMKit.Sym)
    (h : a BitDFT.Unpacker.cntR = TMKit.Sym.one) :
    (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ a).1
        = ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ a).2
          BitDFT.Unpacker.cntR = (TMKit.Sym.blank, IntMul.Move.left) ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ a).2
          BitDFT.Unpacker.inT = (a BitDFT.Unpacker.inT, IntMul.Move.right) :=
  BitDFT.Unpacker.spec_rBinary_mark g κ s a h
