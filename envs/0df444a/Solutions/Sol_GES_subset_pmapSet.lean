-- Prove2me | solution 1 for GES.subset_pmapSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:14:09.83721+00:00
-- url     : https://prove2.me/submissions/530ee1dc-b855-4c14-a484-59ff6eb582d5

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
    {φ : G.Event → Option H.Event} {c : Set G.Event}
    {u : G.Event} {x : H.Event} (hu : u ∈ c) (hx : φ u = some x) : x ∈ pmapSet φ c :=
  ⟨u, hu, hx⟩
end GES
