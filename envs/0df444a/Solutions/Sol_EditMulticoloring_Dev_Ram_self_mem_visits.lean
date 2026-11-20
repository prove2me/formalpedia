-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.self_mem_visits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:33.151621+00:00
-- url     : https://prove2.me/submissions/b96b0fa5-65c6-4504-bc54-78644291261e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamEnum
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

theorem finRange_flatMap {q : ℕ} {β : Type*} (F : Fin q → List β) :
    (List.finRange q).flatMap F = (List.range q).flatMap (finFlat F) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map]
    rw [ih (fun a => F a.castSucc)]
    congr 1
    · apply List.flatMap_congr
      intro a ha
      have ha' : a < n := List.mem_range.mp ha
      simp [finFlat, ha', Nat.lt_succ_of_lt ha']
    · simp [finFlat, Fin.last]

theorem flatMap_filter_eq {α β : Type*} (l : List α) (p : α → Bool) (F : α → List β) :
    (l.filter p).flatMap F = l.flatMap (fun a => if p a then F a else []) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem visits_zero {q : ℕ} (x : Word q) : visits 0 x = [x] := by
  simp [visits, scripts]

theorem visits_succ {q : ℕ} (s : ℕ) (x : Word q) :
    visits (s + 1) x = x ::
      ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a => visits s (insW x i a))) ++
        (List.range x.length).flatMap (fun i => visits s (delW x i)) ++
        (List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a =>
            if x[i]? = some a then [] else visits s (repW x i a)))) := by
  simp only [visits, scripts, List.map_cons, availableEdits, List.flatMap_append, List.map_append,
    List.map_flatMap]
  congr 1
  congr 1
  congr 1
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    rw [List.flatMap_map, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    simp [applyEdit, hi', insW, List.map_map]
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    simp [applyEdit, hi', delW, List.map_map]
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    rw [List.flatMap_map, flatMap_filter_eq, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    by_cases ha : x[i]? = some a
    · simp [ha]
    · have ha2 : ¬ x[i] = a := fun h => ha (by rw [List.getElem?_eq_getElem hi', h])
      simp [applyEdit, hi', ha, ha2, repW, List.map_map]

/-! ## Configuration -/

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator, part 2: the three edit phases (q379, Part L)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Membership in the visit list -/

theorem self_mem_visits_oai {q : ℕ} (k : ℕ) (x : Word q) : x ∈ visits k x := by
  cases k with
  | zero => simp [visits_zero]
  | succ k => rw [visits_succ]; exact List.mem_cons_self

/-! ## Positions in the visit list -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.self_mem_visits_oai := @EditMulticoloring.Dev.Ram.self_mem_visits_oai
