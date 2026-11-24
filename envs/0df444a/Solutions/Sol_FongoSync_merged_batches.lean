-- Prove2me | solution 1 for FongoSync.merged_batches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:28.019871+00:00
-- url     : https://prove2.me/submissions/6cc5be3b-2eaa-4fc5-b898-7abf0a32557d

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
theorem _root_.solution (σ : String → String → Strategy) (b₁ b₂ : List (List (Change V)))
    (same : ∀ b, b ∈ b₁ ↔ b ∈ b₂) (h : ClockDetermines b₁.flatten) :
    merged σ b₁.flatten = merged σ b₂.flatten :=
  merged_eq_of_mem_iff σ _ _ (by simp [same]) h
end FongoSync
