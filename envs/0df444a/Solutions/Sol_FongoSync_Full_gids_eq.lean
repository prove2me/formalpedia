-- Prove2me | solution 1 for FongoSync.Full.gids_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:35.417027+00:00
-- url     : https://prove2.me/submissions/4e7e4d73-eaa2-4a95-b556-32d0f8464a82

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_mem_claimed_iff
import Theorems.Thm_FongoSync_gidSet_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution : gids sc cs₁ = gids sc cs₂ :=
  gidSet_eq_of_mem_iff fun g => by simp only [List.mem_map, mem_claimed_iff sc same]
end FongoSync.Full
