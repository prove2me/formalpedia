-- Prove2me | solution 1 for FongoSync.Full.mem_edges_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:08.260368+00:00
-- url     : https://prove2.me/submissions/ca393f14-acc2-4482-ac6f-79742d2c8b7b

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_home_eq
import Theorems.Thm_FongoSync_Full_unverified_eq
import Theorems.Thm_FongoSync_Full_mem_accepted_iff

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (e : Edge) : e ∈ edges sc cs₁ ↔ e ∈ edges sc cs₂ := by
  unfold edges
  rw [unverified_eq sc same, home_eq sc same]
  simp only [List.mem_filterMap, mem_accepted_iff sc same]
end FongoSync.Full
