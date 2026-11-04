-- Prove2me | solution 1 for BitDFT.unpackerSpec_rUnary_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:55:57.80535+00:00
-- url     : https://prove2.me/submissions/3ce186af-e039-4fe0-b07f-b40289f1a1f0

import Mathlib
import Definitions.Def_BitDFT_unpackerMachineV2
set_option autoImplicit false
noncomputable section
namespace BitDFT.Unpacker

open IntMul TMKit

theorem cntR_ne_inT : cntR ≠ inT := by decide

/-- **The `rUnary` transition rule, written out.**  On a unary mark the phase stays `rUnary`, the
input head steps right keeping its symbol, and the `r`-counter tape receives a mark and steps right. -/
theorem spec_rUnary_mark (g κ s : Bool) (a : Fin 6 → Sym) (h : a inT = Sym.one) :
    (spec ⟨.rUnary, g, κ, s⟩ a).1 = ⟨.rUnary, g, κ, s⟩ ∧
    (spec ⟨.rUnary, g, κ, s⟩ a).2 inT = (a inT, Move.right) ∧
    (spec ⟨.rUnary, g, κ, s⟩ a).2 cntR = (Sym.one, Move.right) ∧
    ∀ i, i ≠ inT → i ≠ cntR → (spec ⟨.rUnary, g, κ, s⟩ a).2 i = (a i, Move.stay) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [spec, h, if_true]
  · simp only [spec, h, if_true, if_pos rfl]
  · simp only [spec, h, if_true, cntR_ne_inT, if_false, if_pos rfl]
  · intro i hi1 hi2
    simp only [spec, h, if_true, hi1, hi2, if_false]

/-- **The `rUnary` exit rule.** -/
theorem spec_rUnary_stop (g κ s : Bool) (a : Fin 6 → Sym) (h : a inT ≠ Sym.one) :
    (spec ⟨.rUnary, g, κ, s⟩ a).1 = ⟨.rSkipFalse, g, κ, s⟩ := by
  simp only [spec, h, if_false, go]

/-- **The guard on the input tape.**  Once the input head has left cell `0` the tape never holds the
end marker, so the guard leaves its symbol alone and passes the phase's move through. -/
theorem guard_inT (q : Q) (a : Fin 6 → Sym) (h : a inT ≠ Sym.start) :
    (guard q a inT).1 = a inT ∧ (guard q a inT).2 = ((spec q a).2 inT).2 := by
  simp [guard, h]

/-- **First per-phase frame transition: `rUnary` reads a mark.**  In phase `rUnary`, with a unary
mark under the input head and the counter head off the end marker, the machine keeps the symbol on
the input tape, steps the input head right, records a mark on the `r`-counter tape and steps that
head right, and does not change phase.

The hypothesis `a cntR ≠ ▷` is not decoration: it is exactly the condition that the superseded
machines violated, and the reason a leading advance phase is needed. -/
theorem rUnary_step (g κ s : Bool) (a : Fin 6 → Sym) (h : a inT = Sym.one)
    (hc0 : a cntR ≠ Sym.start) :
    (spec ⟨.rUnary, g, κ, s⟩ a).1 = ⟨.rUnary, g, κ, s⟩ ∧
    (guard ⟨.rUnary, g, κ, s⟩ a inT).1 = a inT ∧
    (guard ⟨.rUnary, g, κ, s⟩ a inT).2 = Move.right ∧
    (guard ⟨.rUnary, g, κ, s⟩ a cntR).1 = Sym.one ∧
    (guard ⟨.rUnary, g, κ, s⟩ a cntR).2 = Move.right := by
  have hs : a inT ≠ Sym.start := by rw [h]; decide
  have hm := spec_rUnary_mark g κ s a h
  have hg := guard_inT ⟨.rUnary, g, κ, s⟩ a hs
  have hne : cntR ≠ inT := cntR_ne_inT
  have hone : Sym.one ≠ Sym.start := by decide
  have hgc : (guard ⟨.rUnary, g, κ, s⟩ a cntR).1 = Sym.one ∧
      (guard ⟨.rUnary, g, κ, s⟩ a cntR).2 = Move.right := by
    simp only [guard, hc0, if_false]
    rw [if_neg hne, hm.2.2.1]
    simp
  exact ⟨hm.1, hg.1, by rw [hg.2, hm.2.1], hgc.1, hgc.2⟩

end BitDFT.Unpacker

open BitDFT.Unpacker

theorem solution (g κ s : Bool) (a : Fin 6 → TMKit.Sym)
    (h : a BitDFT.Unpacker.inT = TMKit.Sym.one)
    (hc0 : a BitDFT.Unpacker.cntR ≠ TMKit.Sym.start) :
    (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a).1
        = ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.inT).1 = a BitDFT.Unpacker.inT ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.inT).2 = IntMul.Move.right ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.cntR).1 = TMKit.Sym.one ∧
      (BitDFT.Unpacker.guard ⟨BitDFT.Unpacker.Ph.rUnary, g, κ, s⟩ a
          BitDFT.Unpacker.cntR).2 = IntMul.Move.right :=
  BitDFT.Unpacker.rUnary_step g κ s a h hc0
