-- Prove2me | solution 1 for FractionalColouring.fracChromaticNumber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:38.363702+00:00
-- url     : https://prove2.me/submissions/5144c3c3-2e0b-4678-9eaf-49c2b610727c

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_bddBelow_weights

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution {x : Finset V → ℝ} (hx : IsFracColouring G x) :
    fracChromaticNumber G ≤ ∑ s, x s :=
  csInf_le bddBelow_weights ⟨x, hx, rfl⟩
end FractionalColouring
