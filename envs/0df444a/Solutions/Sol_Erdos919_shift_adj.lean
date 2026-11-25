-- Prove2me | solution 1 for Erdos919.shift_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:29:13.834904+00:00
-- url     : https://prove2.me/submissions/ac194d13-52d5-4c17-87ca-77f557058977

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
variable (I : Type*) [LinearOrder I]
variable {I}
namespace Erdos919
theorem _root_.solution {p q : {p : I × I // p.1 < p.2}} :
    (shift I).Adj p q ↔ (p.1.2 = q.1.1 ∨ q.1.2 = p.1.1) := Iff.rfl
end Erdos919
