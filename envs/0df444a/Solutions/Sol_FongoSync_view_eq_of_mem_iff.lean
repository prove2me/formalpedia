-- Prove2me | solution 1 for FongoSync.view_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:30.97857+00:00
-- url     : https://prove2.me/submissions/e02c464c-1c19-4ac9-9900-3aeed712025d

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_view_from_inputs
import Theorems.Thm_FongoSync_inputs_eq
import Theorems.Thm_FongoSync_registers_eq_merged
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_merged_eq_of_mem_iff


set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    view sc cs₁ = view sc cs₂ := by
  apply view_from_inputs
  apply inputs_eq sc same
  rw [registers_eq_merged, registers_eq_merged]
  apply merged_eq_of_mem_iff
  · intro c; simp [same]
  · intro a ha b hb
    exact unique a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1
end FongoSync
