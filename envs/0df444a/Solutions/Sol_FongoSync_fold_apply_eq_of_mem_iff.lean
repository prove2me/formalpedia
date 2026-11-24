-- Prove2me | solution 1 for FongoSync.fold_apply_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:34.105659+00:00
-- url     : https://prove2.me/submissions/f231eac8-0c6c-4416-9390-7e4639f78239

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
import Theorems.Thm_FongoSync_fold_keep_eq_of_mem_iff
import Theorems.Thm_FongoSync_apply_lww
import Theorems.Thm_FongoSync_apply_max
import Theorems.Thm_FongoSync_Entry_pair_inj

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (s : Strategy) (l₁ l₂ : List (Entry V))
    (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (unique : UniqueClocks l₁) :
    l₁.foldl (apply s) none = l₂.foldl (apply s) none := by
  cases s
  · simp only [show apply (V := V) .lww = keep compare Entry.clock from funext fun h => funext fun e => apply_lww h e]
    exact fold_keep_eq_of_mem_iff l₁ l₂ same unique
  · simp only [show apply (V := V) .max = keep maxCmp Entry.pair from funext fun h => funext fun e => apply_max h e]
    exact fold_keep_eq_of_mem_iff l₁ l₂ same fun a _ b _ h => Entry.pair_inj h
end FongoSync
