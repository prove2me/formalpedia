-- Prove2me | solution 1 for GES.toFamily_Config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:37:31.875076+00:00
-- url     : https://prove2.me/submissions/34e020a8-dbb3-4162-9b8a-85638c795d5a

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
theorem _root_.solution : G.toFamily.Config = G.isConf := rfl
end GES
