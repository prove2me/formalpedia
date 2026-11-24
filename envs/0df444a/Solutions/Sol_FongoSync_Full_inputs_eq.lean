-- Prove2me | solution 1 for FongoSync.Full.inputs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:36.434879+00:00
-- url     : https://prove2.me/submissions/25ea70d2-ece1-42f5-9455-b6b89822264e

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_home_eq
import Theorems.Thm_FongoSync_Full_gids_eq
import Theorems.Thm_FongoSync_Full_unverified_eq
import Theorems.Thm_FongoSync_Full_registers_eq
import Theorems.Thm_FongoSync_Full_canon_eq
import Theorems.Thm_FongoSync_IsCanonical_unique


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (unique : ClockDetermines cs₁) : inputs sc cs₁ = inputs sc cs₂ := by
  simp only [inputs, registers_eq sc same unique, home_eq sc same, gids_eq sc same,
    canon_eq sc same unique, unverified_eq sc same]
end FongoSync.Full
