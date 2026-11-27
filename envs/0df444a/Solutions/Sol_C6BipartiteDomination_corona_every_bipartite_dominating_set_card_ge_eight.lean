-- Prove2me | solution 1 for C6BipartiteDomination.corona_every_bipartite_dominating_set_card_ge_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:50.528742+00:00
-- url     : https://prove2.me/submissions/e4eb1007-c099-49e0-8933-75ab7dc22bf8

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_selected_core_card_le_two
import Theorems.Thm_C6BipartiteDomination_corona_core_unselected_card
import Theorems.Thm_C6BipartiteDomination_corona_selected_core_vertices_card
import Theorems.Thm_C6BipartiteDomination_corona_forced_leaves_card
import Theorems.Thm_C6BipartiteDomination_corona_core_leaves_disjoint
import Theorems.Thm_C6BipartiteDomination_corona_core_vertices_subset
import Theorems.Thm_C6BipartiteDomination_corona_forced_leaves_subset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset CoronaVertex} (hD : IsBipartiteDominatingSet coronaGraph D) :
    8 ≤ D.card := by
  classical
  let C := coronaSelectedCore D
  let U := coronaUnselectedCore D
  let K := coronaSelectedCoreVertices D
  let L := coronaForcedLeaves D
  have hKsub : K ⊆ D := corona_core_vertices_subset
  have hLsub : L ⊆ D := corona_forced_leaves_subset hD
  have hdisj : Disjoint K L := corona_core_leaves_disjoint D
  have hUnionSub : K ∪ L ⊆ D := Finset.union_subset hKsub hLsub
  have hLower : C.card + U.card * 2 ≤ D.card := by
    have hCardUnion : (K ∪ L).card = K.card + L.card :=
      Finset.card_union_of_disjoint hdisj
    have hCardLe : (K ∪ L).card ≤ D.card := Finset.card_le_card hUnionSub
    rw [hCardUnion, corona_selected_core_vertices_card, corona_forced_leaves_card] at hCardLe
    exact hCardLe
  have hC : C.card ≤ 2 := corona_selected_core_card_le_two hD
  have hCU : C.card + U.card = 5 := corona_core_unselected_card
  omega
end C6BipartiteDomination
