-- Prove2me | solution 1 for F6ConvexWindow.pairCount_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:46:45.338948+00:00
-- url     : https://prove2.me/submissions/3db2bdc6-d178-40b9-aca3-7d6c67590227

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
theorem _root_.solution (U : Finset V) : pairCount U ≤ U.card.choose 2 := by
  exact (card_filter_le _ _).trans_eq (card_powersetCard 2 U)
end F6ConvexWindow
