-- Prove2me | solution 1 for C6BipartiteDomination.card_PPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:15.778397+00:00
-- url     : https://prove2.me/submissions/4b862383-281f-457b-aaea-38bd2c253655

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
import Theorems.Thm_C6BipartiteDomination_privateExternal_pairwiseDisjoint

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    (PPart G D).card = ∑ b ∈ BPart G D, (privateExternalNeighbors G D b).card := by
  classical
  unfold PPart
  exact Finset.card_biUnion (privateExternal_pairwiseDisjoint G D)
end C6BipartiteDomination
