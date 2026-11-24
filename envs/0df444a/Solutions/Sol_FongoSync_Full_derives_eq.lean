-- Prove2me | solution 1 for FongoSync.Full.derives_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:36.325095+00:00
-- url     : https://prove2.me/submissions/e73bd5c6-cd9b-454c-a659-d245b36e62ae

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_mem_claimed_iff

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution : Derives sc cs₁ = Derives sc cs₂ := by
  funext g c fields k
  simp only [Derives, mem_claimed_iff sc same]
end FongoSync.Full
