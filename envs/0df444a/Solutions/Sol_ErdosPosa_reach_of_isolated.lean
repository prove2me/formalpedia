-- Prove2me | solution 1 for ErdosPosa.reach_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:26.789043+00:00
-- url     : https://prove2.me/submissions/9159c8d8-3c1c-42fa-a349-dadf6fe4add9

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {G : SimpleGraph V} {x y : V} (hx : ∀ z, ¬ G.Adj x z)
    (h : G.Reachable x y) : x = y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hx _)
end ErdosPosa
