-- Prove2me | solution 1 for FairSelling.exists_kept_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:15.766702+00:00
-- url     : https://prove2.me/submissions/e99965f4-b607-43fc-b48b-6ab3b9be834e

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (o : Outcome G n) (E R : Finset G) (T : Finset (Fin n))
    (hdisj : ∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k))
    (hsub : ∀ j, o.kept j \ E ⊆ R)
    (hcard : R.card < T.card) :
    ∃ j ∈ T, o.kept j ⊆ E := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ j ∈ T, (o.kept j \ E).Nonempty := by
    intro j hj
    obtain ⟨g, hg, hgE⟩ := Finset.not_subset.mp (hcon j hj)
    exact ⟨g, Finset.mem_sdiff.mpr ⟨hg, hgE⟩⟩
  have hbi : (T.biUnion fun j => o.kept j \ E).card = ∑ j ∈ T, (o.kept j \ E).card := by
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    exact (hdisj x y hxy).mono Finset.sdiff_subset Finset.sdiff_subset
  have hsub' : (T.biUnion fun j => o.kept j \ E) ⊆ R := by
    intro g hg
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hg
    exact hsub j hj
  have h1 : T.card ≤ ∑ j ∈ T, (o.kept j \ E).card := by
    calc T.card = ∑ _j ∈ T, 1 := by simp
    _ ≤ ∑ j ∈ T, (o.kept j \ E).card :=
        Finset.sum_le_sum fun j hj => Finset.card_pos.mpr (hne j hj)
  have h2 := Finset.card_le_card hsub'
  omega
end FairSelling
