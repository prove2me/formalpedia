-- Prove2me | solution 1 for C6BipartiteDomination.mem_Z0Part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:39.956626+00:00
-- url     : https://prove2.me/submissions/ea486a7e-1c3e-44cd-bb66-d326503420a3

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (z : V) :
    z ∈ Z0Part G D ↔ z ∈ ZPart G D ∧ ∀ w ∈ W0Part G D, ¬ G.Adj z w := by
  classical
  simp [Z0Part]
end C6BipartiteDomination
