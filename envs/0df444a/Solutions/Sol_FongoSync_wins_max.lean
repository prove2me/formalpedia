-- Prove2me | solution 1 for FongoSync.wins_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:38.485802+00:00
-- url     : https://prove2.me/submissions/919b3386-d37f-4d1d-b7d9-03e56663dc25

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Entry V) (v : V) (c : Hlc) :
    wins .max (some s) v c = ((compare s.value v).then (compare s.clock c) == .lt) := by
  simp only [wins]
  rw [OrientedCmp.eq_swap (cmp := (compare : V → V → Ordering)) (a := v) (b := s.value),
    OrientedCmp.eq_swap (cmp := (compare : Hlc → Hlc → Ordering)) (a := c) (b := s.clock)]
  cases compare s.value v <;> cases compare s.clock c <;> rfl
end FongoSync
