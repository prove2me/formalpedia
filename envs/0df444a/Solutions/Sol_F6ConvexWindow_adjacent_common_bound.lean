-- Prove2me | solution 1 for F6ConvexWindow.adjacent_common_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:37:21.995607+00:00
-- url     : https://prove2.me/submissions/6d89c023-0946-40b7-952c-66d01d61d13b

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hci : CI2 (V := V)) {x y : V} (hxy : x < y) :
    (Inc x ∩ Inc y).card ≤ 2 := (hci x y hxy).2
end F6ConvexWindow
