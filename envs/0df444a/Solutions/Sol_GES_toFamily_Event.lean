-- Prove2me | solution 1 for GES.toFamily_Event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:33.410014+00:00
-- url     : https://prove2.me/submissions/4dce0039-63a0-484c-9e0a-9efb3b27d67c

import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Minimal
import Definitions.Def_EventStructures_General_Basic

set_option autoImplicit true
open GES
variable {L : Type*} (G : GES L)
local infix:50 " ⊢ " => G.enable
variable {G}
variable (G)
variable {G}
variable (G)
namespace GES
theorem _root_.solution : G.toFamily.Event = G.Event := rfl
end GES
