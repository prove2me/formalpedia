-- Prove2me | solution 1 for GES.pmapSet_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:14:28.228011+00:00
-- url     : https://prove2.me/submissions/a46b0f50-cf5a-41fe-950a-7e072d038255

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
theorem _root_.solution {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c d : Set G.Event}
    (h : c ⊆ d) : pmapSet φ c ⊆ pmapSet φ d :=
  fun _ ⟨u, hu, hx⟩ => ⟨u, h hu, hx⟩
end GES
