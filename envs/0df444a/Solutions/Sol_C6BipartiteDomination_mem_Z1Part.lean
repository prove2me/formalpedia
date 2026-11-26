-- Prove2me | solution 1 for C6BipartiteDomination.mem_Z1Part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:01.863126+00:00
-- url     : https://prove2.me/submissions/b58ace63-abe8-41b5-8368-38823cade240

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (z : V) :
    z ∈ Z1Part G D ↔
      z ∈ ZPart G D ∧ ∃ w ∈ W0Part G D, G.Adj z w := by
  classical
  simp [Z1Part]
end C6BipartiteDomination
