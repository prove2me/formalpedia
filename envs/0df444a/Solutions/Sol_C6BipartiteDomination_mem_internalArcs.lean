-- Prove2me | solution 1 for C6BipartiteDomination.mem_internalArcs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:35.776345+00:00
-- url     : https://prove2.me/submissions/d8b367e4-4ea2-41ca-b4ca-242ffdffbeaf

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (u v : V) :
    (u, v) ∈ internalArcs G D ↔ u ∈ D ∧ v ∈ D ∧ G.Adj u v := by
  classical
  simp [internalArcs]
end C6BipartiteDomination
