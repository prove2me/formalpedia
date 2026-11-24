-- Prove2me | solution 1 for FairSelling.unifiedOutcome_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:29.723633+00:00
-- url     : https://prove2.me/submissions/bd19523e-7552-4bc4-834a-424699da949b

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hF : ∀ i, Disjoint F (A i))
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i ≤ ∑ g ∈ F, p g) :
    (unifiedOutcome v p A F q).Valid p := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp only [unifiedOutcome]
    rw [Finset.disjoint_union_left]
    refine ⟨Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hF i), ?_⟩
    rw [Finset.disjoint_biUnion_left]
    intro k _
    by_cases hik : k = i
    · subst hik
      exact Finset.disjoint_left.mpr (fun g hg1 hg2 => by
        simp only [Finset.mem_filter] at hg1 hg2; exact hg2.2 hg1.2)
    · exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hA k i hik))
  · intro i j hij
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hA i j hij))
  · intro i
    exact add_nonneg (hq0 i) (Finset.sum_nonneg (fun g _ => hp g))
  · simp only [unifiedOutcome]
    have hdisj : Disjoint F (Finset.univ.biUnion (fun i => (A i).filter (fun g => v i g < p g))) := by
      rw [Finset.disjoint_biUnion_right]
      exact fun i _ => Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hF i)
    rw [Finset.sum_union hdisj]
    have hbu : ∑ g ∈ Finset.univ.biUnion (fun i => (A i).filter (fun g => v i g < p g)), p g
        = ∑ i, ∑ g ∈ (A i).filter (fun g => v i g < p g), p g := by
      rw [Finset.sum_biUnion]
      intro i _ j _ hij
      exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hA i j hij))
    rw [hbu, Finset.sum_add_distrib]
    exact add_le_add hq (le_refl _)
end FairSelling
