-- Prove2me | solution 1 for FongoSync.view_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:58.030382+00:00
-- url     : https://prove2.me/submissions/308ec749-e58a-4a5b-884f-b4a85a77409e

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_view_eq_of_mem_iff
import Theorems.Thm_FongoSync_IsCanonical_unique


set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)} (p : cs₁.Perm cs₂)
    (unique : ClockDetermines cs₁) : view sc cs₁ = view sc cs₂ :=
  view_eq_of_mem_iff sc (fun _ => p.mem_iff) unique
end FongoSync
