-- Prove2me | solution 1 for FongoSync.merged_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:25.33681+00:00
-- url     : https://prove2.me/submissions/892ac09a-69f4-48ec-ad42-866a7e7cb26e

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_merged_eq_of_mem_iff

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (σ : String → String → Strategy) (cs : List (Change V))
    (h : ClockDetermines cs) : merged σ (cs ++ cs) = merged σ cs :=
  merged_eq_of_mem_iff σ _ _ (by simp) (by
    intro a ha b hb; simp only [List.mem_append, or_self] at ha hb; exact h a ha b hb)
end FongoSync
