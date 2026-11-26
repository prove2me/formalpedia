-- Prove2me | solution 1 for C6BipartiteDomination.mem_neighborhoodIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:51.89219+00:00
-- url     : https://prove2.me/submissions/6d99c0a0-6174-4976-b6d3-7c628a123a80

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (q d : V) :
    d ∈ neighborhoodIn G D q ↔ d ∈ D ∧ G.Adj q d := by
  classical
  simp [neighborhoodIn]
end C6BipartiteDomination
