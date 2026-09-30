-- Prove2me | solution 1 for ComplementFreeCA.ValueQuery.alg_maximal_in_range
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:44:29.224251+00:00
-- url     : https://prove2.me/submissions/ec4f8ef5-bc4c-4261-a077-c31482a432dd

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
open Finset ComplementFreeCA.ValueQuery

private theorem matching_alloc_good {n m : ℕ} (μ : Fin m → Option (Fin n)) (hμ : IsMatching μ) :
    IsAllocation (matchingAlloc μ) ∧ ∀ i, (matchingAlloc μ i).card ≤ 1 := by
  refine ⟨?_, ?_⟩
  · intro i i' hne
    apply disjoint_left.mpr
    intro j hj hj'
    simp only [matchingAlloc, mem_filter, mem_univ, true_and] at hj hj'
    exact hne (Option.some.inj (hj.symm.trans hj'))
  · intro i
    apply card_le_one.mpr
    intro j hj j' hj'
    exact hμ j j' i (mem_filter.mp hj).2 (mem_filter.mp hj').2

private theorem matching_welfare {n m : ℕ} (b : Fin n → Finset (Fin m) → ℝ)
    (hb : ∀ i, IsNormalized (b i)) (μ : Fin m → Option (Fin n)) (hμ : IsMatching μ) :
    welfare b (matchingAlloc μ) = matchingWeight b μ := by
  classical
  have hone := (matching_alloc_good μ hμ).2
  have hsingle : ∀ i, b i (matchingAlloc μ i) = ∑ j ∈ matchingAlloc μ i, b i {j} := by
    intro i
    rcases eq_empty_or_nonempty (matchingAlloc μ i) with h | ⟨j, hj⟩
    · simp [h, show b i ∅ = 0 from hb i]
    · have he : matchingAlloc μ i = {j} := by
        ext k
        simp only [mem_singleton]
        constructor
        · intro hk
          exact card_le_one.mp (hone i) k hk j hj
        · intro hk
          subst k
          exact hj
      simp [he]
  unfold welfare
  simp_rw [hsingle]
  simp only [matchingAlloc, sum_filter]
  rw [sum_comm]
  unfold matchingWeight
  apply sum_congr rfl
  intro j hj
  cases h : μ j with
  | none => simp [h]
  | some i => simp [h, eq_comm]

private theorem represent_singletons {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hA : IsAllocation A) (hone : ∀ i, (A i).card ≤ 1) :
    ∃ μ : Fin m → Option (Fin n), IsMatching μ ∧ matchingAlloc μ = A := by
  classical
  let μ : Fin m → Option (Fin n) := fun j => if h : ∃ i, j ∈ A i then some h.choose else none
  have he : ∀ j i, μ j = some i ↔ j ∈ A i := by
    intro j i
    dsimp [μ]
    split_ifs with h
    · constructor
      · intro hi
        rw [← Option.some.inj hi]
        exact h.choose_spec
      · intro hj
        congr 1
        by_contra hne
        exact disjoint_left.mp (hA h.choose i hne) h.choose_spec hj
    · simp only [reduceCtorEq, false_iff]
      exact fun hj => h ⟨i,hj⟩
  refine ⟨μ, ?_, ?_⟩
  · intro j j' i hj hj'
    exact card_le_one.mp (hone i) j ((he j i).mp hj) j' ((he j' i).mp hj')
  · funext i
    ext j
    simp [matchingAlloc, he]

theorem solution {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (hmat : IsMaxWeightMatchingRule mat) (htop : IsTopBidderRule top) :
    IsMaximalInRange IsNormalized ValueQueryRange (alg mat top) := by
  classical
  intro b hb
  have hall : ∀ i, welfare b (allToOne i) = b i univ := by
    intro i
    simp [welfare, allToOne, apply_ite, show ∀ k, b k ∅ = 0 from hb]
  have hmatch := matching_welfare b hb (mat b) (hmat b).1
  have hw : welfare b (alg mat top b) = max (matchingWeight b (mat b)) (b (top b) univ) := by
    unfold alg
    split_ifs with h
    · rw [hall, max_eq_right h.le]
    · rw [hmatch, max_eq_left (le_of_not_gt h)]
  refine ⟨?_, ?_⟩
  · unfold alg
    split_ifs
    · exact Or.inl ⟨top b, rfl⟩
    · exact Or.inr (matching_alloc_good (mat b) (hmat b).1)
  · intro A hA
    rw [hw]
    rcases hA with ⟨i, rfl⟩ | ⟨hA, hone⟩
    · rw [hall]
      exact (htop b i).trans (le_max_right _ _)
    · obtain ⟨μ,hμ,hμA⟩ := represent_singletons A hA hone
      rw [← hμA, matching_welfare b hb μ hμ]
      exact ((hmat b).2 μ hμ).trans (le_max_left _ _)
