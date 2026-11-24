-- Prove2me | solution 1 for FongoSync.Full.view_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:00.946169+00:00
-- url     : https://prove2.me/submissions/6d162760-cf09-4438-9c3f-52642e0501c9

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_inputs_eq
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_inputs_eq


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
namespace FongoSync.Full
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    view sc cs₁ = view sc cs₂ := by
  simp only [view]
  rw [inputs_eq sc (cs₁ := candidates sc cs₁) (cs₂ := candidates sc cs₂)
    (fun c => by simp [candidates, same])
    (fun a ha b hb => unique a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1)]
end FongoSync.Full
