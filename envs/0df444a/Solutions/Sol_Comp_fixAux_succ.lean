-- Prove2me | solution 1 for Comp.fixAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:44:28.13097+00:00
-- url     : https://prove2.me/submissions/cb0e157d-43a7-45f6-9ec1-bd90b273f5c0

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
namespace Comp
theorem _root_.solution (f : Finset S → Finset S) (n : ℕ) (x : Finset S) :
    fixAux f (n + 1) x = if f x = x then x else fixAux f n (f x) := rfl
end Comp
