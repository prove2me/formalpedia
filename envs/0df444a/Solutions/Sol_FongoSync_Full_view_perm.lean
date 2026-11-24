-- Prove2me | solution 1 for FongoSync.Full.view_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:25.392467+00:00
-- url     : https://prove2.me/submissions/d29c47db-b8a7-4206-a279-f08192cf6638

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_view_eq_of_mem_iff
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_view_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
namespace FongoSync.Full
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)} (p : cs₁.Perm cs₂)
    (unique : ClockDetermines cs₁) : view sc cs₁ = view sc cs₂ :=
  view_eq_of_mem_iff sc (fun _ => p.mem_iff) unique
end FongoSync.Full
