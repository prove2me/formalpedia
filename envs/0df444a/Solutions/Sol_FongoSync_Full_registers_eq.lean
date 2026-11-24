-- Prove2me | solution 1 for FongoSync.Full.registers_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:06.996328+00:00
-- url     : https://prove2.me/submissions/15dd0bb7-f212-435f-813c-9477bb09e9e4

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_mem_accepted_iff
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_merged_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (unique : ClockDetermines cs₁) : registers sc cs₁ = registers sc cs₂ := by
  apply merged_eq_of_mem_iff
  · intro c; simp only [List.mem_filter, mem_accepted_iff sc same]
  · intro a ha b hb
    have hsub : ∀ x, x ∈ (accepted sc cs₁).filter (fun c => c.field ≠ ALIAS) → x ∈ cs₁ := by
      intro x hx
      simp only [List.mem_filter, accepted, claimed] at hx
      exact hx.1.1.1
    exact unique a (hsub a ha) b (hsub b hb)
end FongoSync.Full
