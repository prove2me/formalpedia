-- Prove2me | solution 1 for FongoSync.Full.key_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:00.88451+00:00
-- url     : https://prove2.me/submissions/bd596161-2439-465b-b408-bfaa4d2c76ce

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_homeCollection_eq
import Theorems.Thm_FongoSync_Full_derives_eq

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution : key sc cs₁ = key sc cs₂ := by
  funext g
  unfold key
  rw [homeCollection_eq sc same, derives_eq sc same]
end FongoSync.Full
