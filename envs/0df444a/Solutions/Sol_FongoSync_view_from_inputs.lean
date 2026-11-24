-- Prove2me | solution 1 for FongoSync.view_from_inputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:47.95747+00:00
-- url     : https://prove2.me/submissions/c7151b21-4e7d-4fb7-a8e5-f2e8927dd241

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (h : inputs sc cs₁ = inputs sc cs₂) : view sc cs₁ = view sc cs₂ := by
  simp only [view, h]
end FongoSync
