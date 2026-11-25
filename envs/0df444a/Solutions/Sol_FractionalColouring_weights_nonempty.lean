-- Prove2me | solution 1 for FractionalColouring.weights_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:04.125866+00:00
-- url     : https://prove2.me/submissions/0fd96429-1c13-4cb5-a5fb-dc557b648c72

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_isFracColouring_singletons

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution : {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s}.Nonempty :=
  ⟨_, _, isFracColouring_singletons, rfl⟩
end FractionalColouring
