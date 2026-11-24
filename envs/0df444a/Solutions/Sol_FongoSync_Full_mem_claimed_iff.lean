-- Prove2me | solution 1 for FongoSync.Full.mem_claimed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:49.788491+00:00
-- url     : https://prove2.me/submissions/b59d2b54-1613-4837-a2d4-0e0209a517a2

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_home_eq

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (c : Change Value) : c ∈ claimed sc cs₁ ↔ c ∈ claimed sc cs₂ := by
  simp only [claimed, List.mem_filter, same, home_eq sc same]
end FongoSync.Full
