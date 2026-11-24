-- Prove2me | solution 1 for FongoSync.apply_lww
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:04.953285+00:00
-- url     : https://prove2.me/submissions/20570f9f-81c4-414c-8d6e-3c9ddd5f3d46

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
namespace FongoSync
theorem _root_.solution (held : Option (Entry V)) (e : Entry V) :
    apply .lww held e = keep compare Entry.clock held e := by
  cases held with
  | none => rfl
  | some s =>
    simp only [apply, wins, keep_held]
    have := OrientedCmp.gt_iff_lt (cmp := (compare : Hlc → Hlc → Ordering)) (a := e.clock) (b := s.clock)
    by_cases h : compare s.clock e.clock = .lt <;> simp_all
end FongoSync
