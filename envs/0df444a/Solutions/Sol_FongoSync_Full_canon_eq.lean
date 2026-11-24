-- Prove2me | solution 1 for FongoSync.Full.canon_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:59.543339+00:00
-- url     : https://prove2.me/submissions/0074e6d4-9181-4d6a-a1c0-58f88dca94c5

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_groupedAt_eq
import Theorems.Thm_FongoSync_IsCanonical_unique


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (unique : ClockDetermines cs₁) : canon sc cs₁ = canon sc cs₂ := by
  have : Grouped sc cs₁ = Grouped sc cs₂ := by
    funext a b; simp only [Grouped, groupedAt_eq sc same unique]
  funext g; unfold canon; rw [this]
end FongoSync.Full
