-- Prove2me | solution 1 for C6BipartiteDomination.private_card_eq_two_add_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:21.013718+00:00
-- url     : https://prove2.me/submissions/ede1e0e7-16e4-4667-972f-5c9beb21fd3d

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_nonisolated_of_mem_BPart
import Theorems.Thm_C6BipartiteDomination_lemma_3_1_private_neighbors


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D) {b : V}
    (hb : b ∈ BPart G D) :
    (privateExternalNeighbors G D b).card = 2 + xCharge G D b := by
  have htwo := lemma_3_1_private_neighbors G hCan
    (nonisolated_of_mem_BPart G hb)
  unfold xCharge
  omega
end C6BipartiteDomination
