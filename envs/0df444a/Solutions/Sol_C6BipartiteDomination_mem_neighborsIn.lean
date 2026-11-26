-- Prove2me | solution 1 for C6BipartiteDomination.mem_neighborsIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:25.502205+00:00
-- url     : https://prove2.me/submissions/38e58103-8e89-4e6b-bad1-8b47417d7d07

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (S T : Finset V) (w : V) :
    w ∈ neighborsIn G S T ↔ w ∈ T ∧ ∃ v ∈ S, G.Adj v w := by
  classical
  simp [neighborsIn]
end C6BipartiteDomination
