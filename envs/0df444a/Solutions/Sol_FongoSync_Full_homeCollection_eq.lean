-- Prove2me | solution 1 for FongoSync.Full.homeCollection_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:46.064439+00:00
-- url     : https://prove2.me/submissions/7a05c9ca-ac22-4724-abdb-31f62df8e424

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
theorem _root_.solution : homeCollection sc cs₁ = homeCollection sc cs₂ := by
  funext g; simp only [homeCollection, home_eq sc same]
end FongoSync.Full
