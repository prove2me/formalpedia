-- Prove2me | solution 1 for C6BipartiteDomination.mem_sharedCompensation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:24.837849+00:00
-- url     : https://prove2.me/submissions/17a652c6-4808-47e8-80df-b54e4f84e62e

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D X : Finset V) (u q : V) :
    q ∈ sharedCompensation G D X u ↔
      q ∉ D ∧ ∃ z ∈ X, neighborhoodIn G D q = {u, z} := by
  classical
  simp [sharedCompensation]
end C6BipartiteDomination
