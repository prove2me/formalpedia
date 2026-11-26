-- Prove2me | solution 1 for C6BipartiteDomination.lemma_3_1_private_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:35.663403+00:00
-- url     : https://prove2.me/submissions/cbadf786-b041-49be-b54d-753d6fcc1510

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
import Theorems.Thm_C6BipartiteDomination_empty_privateExternalNeighbors_contradiction
import Theorems.Thm_C6BipartiteDomination_singleton_privateExternalNeighbors_contradiction

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {b : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b) :
    2 ≤ (privateExternalNeighbors G D b).card := by
  classical
  by_contra hsmall
  have hcases : (privateExternalNeighbors G D b).card = 0 ∨
      (privateExternalNeighbors G D b).card = 1 := by omega
  rcases hcases with hzero | hone
  · have hPempty : privateExternalNeighbors G D b = ∅ :=
      Finset.card_eq_zero.mp hzero
    exact (empty_privateExternalNeighbors_contradiction G hCan hb hPempty).elim
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hone
    have hPsingle : privateExternalNeighbors G D b = {p} := hp
    exact (singleton_privateExternalNeighbors_contradiction G hCan hb hPsingle).elim
end C6BipartiteDomination
