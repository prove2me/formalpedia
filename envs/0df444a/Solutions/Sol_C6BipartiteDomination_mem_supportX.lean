-- Prove2me | solution 1 for C6BipartiteDomination.mem_supportX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:40.880155+00:00
-- url     : https://prove2.me/submissions/5d510ac2-dd25-41e7-89fd-85d83a12b5aa

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (w z : V) :
    z ∈ supportX G D w ↔ z ∈ Z0Part G D ∧ G.Adj w z := by
  classical
  simp [supportX]
end C6BipartiteDomination
