-- Prove2me | solution 1 for F6ConvexWindow.card_crossPairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:14:04.010112+00:00
-- url     : https://prove2.me/submissions/5c5d2a91-4842-410a-943e-91f61dae1367

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
theorem _root_.solution (U W : Finset V) : (crossPairs U W).card ≤ crossCount U W := by
  classical
  apply (card_biUnion_le).trans
  exact sum_le_sum (fun x _ => card_image_le)
end F6ConvexWindow
