-- Prove2me | solution 1 for FairChores.exists_outcome_of_preAlloc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:28.930385+00:00
-- url     : https://prove2.me/submissions/e67ef9cc-d1ec-4490-9f40-f16ad29f32e3

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (P : PreAlloc T n) (p : T → ℝ) (c : Fin n → T → ℝ)
    (hp : ∀ t, 0 ≤ p t)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P.bundle i) (P.bundle j))
    (houts : ∀ i, Disjoint P.outs (P.bundle i))
    (hcover : P.outs ∪ Finset.univ.biUnion P.bundle = Finset.univ)
    (hshare : ∀ i, 0 ≤ P.share i)
    (hsum : ∑ i, P.share i = ∑ t ∈ P.outs, p t) :
    ∃ o : Outcome T n, o.Valid p ∧
      ∀ i, cost (c i) o i = cbarSum (c i) p (P.bundle i) + P.share i := by
  classical
  -- the chores of `bundle i` that agent `i` prefers to outsource
  set sold : Fin n → Finset T := fun i => (P.bundle i).filter (fun t => p t < c i t) with hsold
  set done : Fin n → Finset T := fun i => (P.bundle i).filter (fun t => ¬ p t < c i t) with hdone
  have hsplit : ∀ i, (sold i) ∪ (done i) = P.bundle i := by
    intro i
    rw [hsold, hdone]
    exact Finset.filter_union_filter_not_eq _ _
  have hsd : ∀ i, Disjoint (sold i) (done i) := by
    intro i
    refine Finset.disjoint_left.mpr fun t ht ht' => ?_
    simp only [hsold, hdone, Finset.mem_filter] at ht ht'
    exact ht'.2 ht.2
  have hsub_sold : ∀ i, sold i ⊆ P.bundle i := fun i => Finset.filter_subset _ _
  have hsub_done : ∀ i, done i ⊆ P.bundle i := fun i => Finset.filter_subset _ _
  refine ⟨⟨P.outs ∪ Finset.univ.biUnion sold, done, fun i => P.share i + ∑ t ∈ sold i, p t⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- outsourced chores are not performed
    intro j
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact Finset.disjoint_of_subset_right (hsub_done j) (houts j)
    · refine Finset.disjoint_left.mpr fun t ht ht' => ?_
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp ht
      by_cases hij : i = j
      · subst hij
        exact Finset.disjoint_left.mp (hsd i) hi ht'
      · exact Finset.disjoint_left.mp (hdisj i j hij) (hsub_sold i hi) (hsub_done j ht')
  · intro j k hjk
    exact Finset.disjoint_of_subset_left (hsub_done j)
      (Finset.disjoint_of_subset_right (hsub_done k) (hdisj j k hjk))
  · -- every chore is either outsourced or performed
    rw [← hcover]
    ext t
    simp only [Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (⟨h | ⟨i, -, hi⟩⟩ | ⟨i, -, hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, Finset.mem_univ i, hsub_sold i hi⟩
      · exact Or.inr ⟨i, Finset.mem_univ i, hsub_done i hi⟩
    · rintro (h | ⟨i, -, hi⟩)
      · exact Or.inl (Or.inl h)
      · rw [← hsplit i] at hi
        rcases Finset.mem_union.mp hi with h | h
        · exact Or.inl (Or.inr ⟨i, Finset.mem_univ i, h⟩)
        · exact Or.inr ⟨i, Finset.mem_univ i, h⟩
  · intro j
    have h1 : (0:ℝ) ≤ ∑ t ∈ sold j, p t := Finset.sum_nonneg fun t _ => hp t
    linarith [hshare j, h1]
  · -- the outsourcing bill is exactly covered
    have hdisj2 : Disjoint P.outs (Finset.univ.biUnion sold) := by
      refine Finset.disjoint_left.mpr fun t ht ht' => ?_
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp ht'
      exact Finset.disjoint_left.mp (houts i) ht (hsub_sold i hi)
    rw [Finset.sum_union hdisj2,
      Finset.sum_biUnion (fun i _ j _ hij => Finset.disjoint_of_subset_left (hsub_sold i)
        (Finset.disjoint_of_subset_right (hsub_sold j) (hdisj i j hij))),
      Finset.sum_add_distrib, hsum]
  · -- the cost of agent `i`
    intro i
    have : cbarSum (c i) p (P.bundle i)
        = (∑ t ∈ sold i, p t) + ∑ t ∈ done i, c i t := by
      rw [cbarSum, ← hsplit i, Finset.sum_union (hsd i)]
      congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        simp only [hsold, Finset.mem_filter] at ht
        simp [cbar, min_eq_right (le_of_lt ht.2)]
      · refine Finset.sum_congr rfl fun t ht => ?_
        simp only [hdone, Finset.mem_filter] at ht
        simp [cbar, min_eq_left (not_lt.mp ht.2)]
    simp only [cost]
    rw [this]
    ring
end FairChores
