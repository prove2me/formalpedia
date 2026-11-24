-- Prove2me | solution 1 for FongoSync.known_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:38.120986+00:00
-- url     : https://prove2.me/submissions/62ade9bd-6279-4084-b83e-2247650b705b

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_mem_ours_iff
import Theorems.Thm_FongoSync_gidSet_eq_of_mem_iff


set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) :
    known sc cs₁ = known sc cs₂ :=
  gidSet_eq_of_mem_iff fun g => by simp only [List.mem_map, mem_ours_iff sc same]
end FongoSync
