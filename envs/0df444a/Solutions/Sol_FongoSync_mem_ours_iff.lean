-- Prove2me | solution 1 for FongoSync.mem_ours_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:00:49.346272+00:00
-- url     : https://prove2.me/submissions/50a59999-51f3-4f42-979f-35fb013f641b

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
    (c : Change Value) : c ∈ ours sc cs₁ ↔ c ∈ ours sc cs₂ := by
  simp [ours, same]
end FongoSync
