-- Prove2me | solution 1 for FongoSync.inputs_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:07.419473+00:00
-- url     : https://prove2.me/submissions/6c0cc68c-9140-4fc8-a6d0-512a6022109f

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_mem_ours_iff
import Theorems.Thm_FongoSync_known_eq
import Theorems.Thm_FongoSync_canonical_eq_of_mem_iff


set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
    (regs : registers sc cs₁ = registers sc cs₂) : inputs sc cs₁ = inputs sc cs₂ := by
  have hk := known_eq sc same
  have he : ∀ e, e ∈ edges sc cs₁ ↔ e ∈ edges sc cs₂ := by
    intro e
    simp only [edges, List.mem_filterMap, mem_ours_iff sc same, hk]
  simp only [inputs, regs, hk, canonical_eq_of_mem_iff _ _ he]
end FongoSync
