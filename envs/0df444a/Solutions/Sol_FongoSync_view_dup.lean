-- Prove2me | solution 1 for FongoSync.view_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:01.904299+00:00
-- url     : https://prove2.me/submissions/e52aac5e-81c1-4fb9-b121-2643b3251f25

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
theorem _root_.solution (sc : Schema) (cs : List (Change Value)) (unique : ClockDetermines cs) :
    view sc (cs ++ cs) = view sc cs :=
  view_eq_of_mem_iff sc (by simp) (by
    intro a ha b hb; simp only [List.mem_append, or_self] at ha hb; exact unique a ha b hb)
end FongoSync
