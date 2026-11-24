-- Prove2me | solution 1 for FongoSync.Full.view_ignores_unencodable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:06.079333+00:00
-- url     : https://prove2.me/submissions/48bd0ea4-ba4e-4bd9-ad2a-907b640d6820

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_view_ignores

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
namespace FongoSync.Full
theorem _root_.solution (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : ¬ c.clock.encodable) : view sc (c :: cs) = view sc cs :=
  view_ignores sc c cs fun h' => h h'.1
end FongoSync.Full
