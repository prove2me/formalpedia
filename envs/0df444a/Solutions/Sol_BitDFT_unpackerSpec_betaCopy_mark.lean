-- Prove2me | solution 1 for BitDFT.unpackerSpec_betaCopy_mark
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:22.717268+00:00
-- url     : https://prove2.me/submissions/c9c1696c-1992-458a-a33b-d080bcb6a5a9

import Mathlib
import Definitions.Def_BitDFT_unpackerMachineV6
set_option autoImplicit false
noncomputable section
namespace BitDFT.Unpacker
open IntMul TMKit

theorem cnt_ne_tpl : cnt ≠ tpl := by decide
theorem cnt_ne_inT : cnt ≠ inT := by decide
theorem tpl_ne_inT : tpl ≠ inT := by decide

/-- **The `β`-copy rule on a mark.**  The phase keeps its name, erases the counter's mark and steps
that head left, writes the symbol under the input head onto the template and steps the template head
right, and advances the input head one cell. -/
theorem spec_betaCopyGo_mark (g κ s : Bool) (a : Fin 6 → Sym) (h : a cnt = Sym.one) :
    (spec ⟨.betaCopyGo, g, κ, s⟩ a).1 = ⟨.betaCopyGo, g, κ, s⟩ ∧
    (spec ⟨.betaCopyGo, g, κ, s⟩ a).2 cnt = (Sym.blank, Move.left) ∧
    (spec ⟨.betaCopyGo, g, κ, s⟩ a).2 tpl = (a inT, Move.right) ∧
    (spec ⟨.betaCopyGo, g, κ, s⟩ a).2 inT = (a inT, Move.right) ∧
    ∀ i, i ≠ cnt → i ≠ tpl → i ≠ inT → (spec ⟨.betaCopyGo, g, κ, s⟩ a).2 i = (a i, Move.stay) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [spec, h, if_true]
  · simp only [spec, h, if_true, if_pos rfl]
  · simp only [spec, h, if_true, if_pos rfl]
    rw [if_neg (Ne.symm cnt_ne_tpl)]
  · simp only [spec, h, if_true, if_pos rfl]
    rw [if_neg (Ne.symm cnt_ne_inT)]
    rw [if_neg (Ne.symm tpl_ne_inT)]
  · intro i h1 h2 h3
    simp only [spec, h, if_true, h1, h2, h3, if_false]

end BitDFT.Unpacker

theorem solution (g κ s : Bool) (a : Fin 6 → TMKit.Sym)
    (h : a BitDFT.Unpacker.cnt = TMKit.Sym.one) :
    (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).1
        = ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2
          BitDFT.Unpacker.cnt = (TMKit.Sym.blank, IntMul.Move.left) ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2
          BitDFT.Unpacker.tpl = (a BitDFT.Unpacker.inT, IntMul.Move.right) ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2
          BitDFT.Unpacker.inT = (a BitDFT.Unpacker.inT, IntMul.Move.right) ∧
      ∀ i, i ≠ BitDFT.Unpacker.cnt → i ≠ BitDFT.Unpacker.tpl → i ≠ BitDFT.Unpacker.inT →
        (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2 i
          = (a i, IntMul.Move.stay) :=
  BitDFT.Unpacker.spec_betaCopyGo_mark g κ s a h
