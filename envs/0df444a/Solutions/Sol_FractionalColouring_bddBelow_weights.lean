-- Prove2me | solution 1 for FractionalColouring.bddBelow_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:47.48618+00:00
-- url     : https://prove2.me/submissions/0b9069d0-bcd4-4440-8a01-2a4e5125ef62

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution : BddBelow {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s} :=
  ⟨0, by
    rintro _ ⟨x, hx, rfl⟩
    exact Finset.sum_nonneg fun s _ => hx.1 s⟩
end FractionalColouring
