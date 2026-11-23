-- Prove2me | solution 1 for DecisionTree.usesVar_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:42.963508+00:00
-- url     : https://prove2.me/submissions/b167da44-f8a9-455e-a41e-39a09d1f27b9

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree

set_option autoImplicit true
open DecisionTree
namespace DecisionTree
theorem _root_.solution (i : Fin n) (T : DecisionTree n) :
    T.usesVar i ↔ (∃ i' l h, T = .branch i' l h ∧ (i = i' ∨ l.usesVar i ∨ h.usesVar i)) := by
  constructor
  · intro h
    cases h with
    | here => simp
    | low hl => simp [hl]
    | high hh => simp [hh]
  · rintro ⟨i', l, h, h1, h2⟩
    cases h2 with
    | inl => simp_all [usesVar.here]
    | inr h2 =>
      cases h2 with
      | inl => simp_all [usesVar.low]
      | inr => simp_all [usesVar.high]
end DecisionTree
