-- Prove2me | solution 1 for FFactor.label_eq_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:44.808686+00:00
-- url     : https://prove2.me/submissions/81eec97c-28ab-47ce-96d8-34fd11ed32eb

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {X L : Type*} (H : SimpleGraph X) (φ : X → L)
namespace FFactor
theorem _root_.solution (h1 : ∀ x y, H.Adj x y → φ x = φ y) {x y : X}
    (h : H.Reachable x y) : φ x = φ y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (h1 _ _ ha).trans ih
end FFactor
