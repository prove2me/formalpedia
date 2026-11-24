-- Prove2me | solution 1 for FongoSync.Full.view_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:31.887849+00:00
-- url     : https://prove2.me/submissions/47de409d-ff68-41c0-b791-a84bc968bbf4

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
theorem _root_.solution (sc : Schema) (cs : List (Change Value)) (unique : ClockDetermines cs) :
    view sc (cs ++ cs) = view sc cs :=
  view_eq_of_mem_iff sc (by simp) (by
    intro a ha b hb; simp only [List.mem_append, or_self] at ha hb; exact unique a ha b hb)
end FongoSync.Full
