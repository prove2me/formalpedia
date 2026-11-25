-- Prove2me | solution 1 for F6ConvexWindow.card_tripleFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:32:22.303006+00:00
-- url     : https://prove2.me/submissions/db0f3693-6355-4b3a-8517-61fffedb263a

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution : (tripleFamily (V := V)).card = Ak (V := V) 3 := rfl
end F6ConvexWindow
