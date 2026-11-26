-- Prove2me | solution 1 for C6BipartiteDomination.corona_vertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:34.687373+00:00
-- url     : https://prove2.me/submissions/6eac003a-11bc-44d6-b839-be3e5a0c853a

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution : Fintype.card CoronaVertex = 15 := by
  simp [CoronaVertex]
end C6BipartiteDomination
