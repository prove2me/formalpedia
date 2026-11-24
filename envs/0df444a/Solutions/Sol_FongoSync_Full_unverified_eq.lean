-- Prove2me | solution 1 for FongoSync.Full.unverified_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:38.804204+00:00
-- url     : https://prove2.me/submissions/cbe4da33-4967-43b1-a3ba-dd28b781ce31

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_homeCollection_eq
import Theorems.Thm_FongoSync_Full_key_eq

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution : Unverified sc cs₁ = Unverified sc cs₂ := by
  funext g
  simp only [Unverified, homeCollection_eq sc same, key_eq sc same]
end FongoSync.Full
