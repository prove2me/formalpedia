-- Prove2me | solution 2 for GES.pmapSet_mono
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:14:58.925958+00:00
-- url     : https://prove2.me/submissions/8714591a-c631-4b2d-ae7e-654e754683f3

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

theorem GES.pmapSet_mono {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c d : Set G.Event}
    (h : c ⊆ d) : pmapSet φ c ⊆ pmapSet φ d := by
  rintro x ⟨u, hu, hx⟩
  exact ⟨u, h hu, hx⟩

theorem solution {L' : Type*} {G : GES L} {H : GES L'}
    {φ : G.Event → Option H.Event} {c d : Set G.Event}
    (h : c ⊆ d) : pmapSet φ c ⊆ pmapSet φ d := GES.pmapSet_mono h
