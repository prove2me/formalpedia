-- Prove2me | solution 1 for FongoSync.merged_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:24.845806+00:00
-- url     : https://prove2.me/submissions/52557eb3-0f7a-4886-937b-af7493a42c7f

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
theorem _root_.solution (σ : String → String → Strategy) {cs₁ cs₂ : List (Change V)}
    (p : cs₁.Perm cs₂) (h : ClockDetermines cs₁) : merged σ cs₁ = merged σ cs₂ :=
  merged_eq_of_mem_iff σ cs₁ cs₂ (fun _ => p.mem_iff) h
end FongoSync
