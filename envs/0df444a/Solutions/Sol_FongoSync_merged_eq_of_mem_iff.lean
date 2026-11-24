-- Prove2me | solution 1 for FongoSync.merged_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:58.444958+00:00
-- url     : https://prove2.me/submissions/c7cb3b8f-3988-4583-b84e-7c1bf2395bee

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_merged_at
import Theorems.Thm_FongoSync_mem_entriesAt
import Theorems.Thm_FongoSync_uniqueClocks_entriesAt
import Theorems.Thm_FongoSync_fold_apply_eq_of_mem_iff


set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
theorem _root_.solution (σ : String → String → Strategy) (cs₁ cs₂ : List (Change V))
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (h : ClockDetermines cs₁) :
    merged σ cs₁ = merged σ cs₂ := by
  funext k
  rw [merged_at, merged_at]
  apply fold_apply_eq_of_mem_iff _ _ _ _ (uniqueClocks_entriesAt h k)
  intro e
  simp only [mem_entriesAt, same]
end FongoSync
