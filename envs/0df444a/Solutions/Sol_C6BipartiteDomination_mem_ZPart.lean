-- Prove2me | solution 1 for C6BipartiteDomination.mem_ZPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:33.157791+00:00
-- url     : https://prove2.me/submissions/3e14ddfd-eb8a-4f1d-b660-4b20e1705582

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (z : V) :
    z ∈ ZPart G D ↔ z ∈ D ∧ ∀ u ∈ D, ¬ G.Adj z u := by
  classical
  simp [ZPart]
end C6BipartiteDomination
