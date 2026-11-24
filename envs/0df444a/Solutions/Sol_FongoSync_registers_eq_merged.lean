-- Prove2me | solution 1 for FongoSync.registers_eq_merged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:38.570738+00:00
-- url     : https://prove2.me/submissions/1e12f1a2-e69b-4e91-9f0c-ca97b6d28814

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false
namespace FongoSync
theorem _root_.solution (sc : Schema) (cs : List (Change Value)) :
    registers sc cs = merged sc.strategyOf (cs.filter fun c => c.field ≠ ALIAS) := by
  simp only [registers, merged, List.foldl_filter]
  congr
  funext st c
  by_cases h : c.field = ALIAS <;> simp [h, step]
end FongoSync
