-- Prove2me | solution 1 for C6BipartiteDomination.mem_privateExternalNeighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:18.106628+00:00
-- url     : https://prove2.me/submissions/ec7a23c8-7b81-4331-98d5-df372baa5c56

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (b w : V) :
    w ∈ privateExternalNeighbors G D b ↔
      w ∉ D ∧ ∀ u ∈ D, G.Adj u w ↔ u = b := by
  classical
  simp [privateExternalNeighbors]
end C6BipartiteDomination
