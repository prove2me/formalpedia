-- Prove2me | solution 1 for FongoSync.Full.mem_accepted_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:39.405736+00:00
-- url     : https://prove2.me/submissions/be92f7e0-75ee-4943-9e7c-b8f0dbf28370

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_mem_claimed_iff
import Theorems.Thm_FongoSync_Full_homeCollection_eq
import Theorems.Thm_FongoSync_Full_key_eq

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (c : Change Value) : c ∈ accepted sc cs₁ ↔ c ∈ accepted sc cs₂ := by
  have : keyFieldOk sc cs₁ = keyFieldOk sc cs₂ := by
    funext x; unfold keyFieldOk; rw [homeCollection_eq sc same, key_eq sc same]
  simp only [accepted, List.mem_filter, mem_claimed_iff sc same, this]
end FongoSync.Full
