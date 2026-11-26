-- Prove2me | solution 1 for C6BipartiteDomination.corona_core_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:17.354546+00:00
-- url     : https://prove2.me/submissions/670132bd-98d8-4667-96ad-c3ed50a5367f

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_core_neighbor_finset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (i : Fin 5) :
    degreeTo coronaGraph Finset.univ (Sum.inl i) = 6 := by
  classical
  unfold degreeTo
  rw [corona_core_neighbor_finset]
  have hdisj : Disjoint
      ((Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex)))
      ({Sum.inr (i, 0), Sum.inr (i, 1)} : Finset CoronaVertex) := by
    rw [Finset.disjoint_left]
    intro v hvC hvL
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvC
    simp at hvL
  rw [Finset.card_union_of_disjoint hdisj]
  have hcore :
      ((Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex))).card = 4 := by
    rw [Finset.card_image_of_injective _ (by
      intro a b hab
      exact Sum.inl.inj hab)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hcore]
  simp
end C6BipartiteDomination
