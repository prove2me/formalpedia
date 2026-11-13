-- Prove2me | solution 1 for CountingLLL.DetCount.corollary_2_6
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:44:33.428462+00:00
-- url     : https://prove2.me/submissions/7be3d08a-4822-4186-ab59-1cc09aaa65d9

import Definitions.Def_CountingLLL_DetCount_TwoTree
import Theorems.Thm_CountingLLL_DetCount_lemma_2_5

set_option autoImplicit false

open CountingLLL.DetCount

private noncomputable def twoNbrs {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (u : V) : Finset V := by
  classical
  exact G.neighborFinset u ∪ (G.neighborFinset u).biUnion (fun w => (G.neighborFinset w).erase u)

private theorem square_subset {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (u v : V)
    (h : (square G).Adj u v) : v ∈ twoNbrs G u := by
  classical
  rcases h with ⟨hne, hdist⟩
  by_cases hadj : G.Adj u v
  · apply Finset.mem_union_left
    simpa using hadj
  · have hcommon : (G.commonNeighbors u v).Nonempty := by
      by_contra hn
      have he : G.commonNeighbors u v = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      have := G.two_lt_edist_iff.mpr ⟨hne, hadj, he⟩
      exact (not_lt_of_ge hdist) this
    obtain ⟨w, hw⟩ := hcommon
    rw [SimpleGraph.mem_commonNeighbors] at hw
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, ?_⟩
    · simpa using hw.1
    · apply Finset.mem_erase.mpr
      exact ⟨hne.symm, by simpa using hw.2.symm⟩

private noncomputable def square_locallyFinite {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] :
    (square G).LocallyFinite := by
  classical
  intro u
  let s : Set V := (twoNbrs G u : Set V)
  have hs : s.Finite := (twoNbrs G u).finite_toSet
  exact (hs.subset (fun v hv => square_subset G u v hv)).fintype

private theorem twoNbrs_card_le {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (Δ : ℕ) (hΔ : ∀ u, G.degree u ≤ Δ) (u : V) : (twoNbrs G u).card ≤ Δ^2 := by
  classical
  have hsum : (∑ w ∈ G.neighborFinset u, ((G.neighborFinset w).erase u).card) ≤
      (G.degree u) * (Δ - 1) := by
    calc
      _ ≤ ∑ _w ∈ G.neighborFinset u, (Δ - 1) := by
        apply Finset.sum_le_sum
        intro w hw
        have hu : u ∈ G.neighborFinset w := by
          rw [G.mem_neighborFinset] at hw ⊢
          exact hw.symm
        rw [Finset.card_erase_of_mem hu, G.card_neighborFinset_eq_degree]
        exact Nat.sub_le_sub_right (hΔ w) 1
      _ = (G.degree u) * (Δ - 1) := by simp [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have hbound : (twoNbrs G u).card ≤ G.degree u + G.degree u * (Δ - 1) := by
    calc
      _ ≤ (G.neighborFinset u).card + ((G.neighborFinset u).biUnion (fun w => (G.neighborFinset w).erase u)).card := Finset.card_union_le _ _
      _ ≤ (G.neighborFinset u).card + ∑ w ∈ G.neighborFinset u, ((G.neighborFinset w).erase u).card := Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ G.degree u + G.degree u * (Δ - 1) := by simpa only [G.card_neighborFinset_eq_degree] using Nat.add_le_add_left hsum (G.degree u)
  have hdeg := hΔ u
  by_cases h0 : Δ = 0
  · subst Δ
    simp only [Nat.le_zero] at hdeg
    simp [hdeg] at hbound ⊢
    exact hbound
  · have hd : 1 ≤ Δ := Nat.one_le_iff_ne_zero.mpr h0
    have he : Δ - 1 + 1 = Δ := Nat.sub_add_cancel hd
    nlinarith

private theorem square_degree_le {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (Δ : ℕ) (hΔ : ∀ u, G.degree u ≤ Δ) (u : V) :
    letI : (square G).LocallyFinite := square_locallyFinite G
    (square G).degree u ≤ Δ^2 := by
  classical
  letI : (square G).LocallyFinite := square_locallyFinite G
  calc
    (square G).degree u = ((square G).neighborFinset u).card := rfl
    _ ≤ (twoNbrs G u).card := by
      apply Finset.card_le_card
      intro v hv
      exact square_subset G u v ((square G).mem_neighborFinset u v |>.mp hv)
    _ ≤ Δ^2 := twoNbrs_card_le G Δ hΔ u

theorem solution {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ : ∀ u, G.degree u ≤ Δ) (v : V) (ℓ : ℕ) :
    {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ IsTwoTree G S}.Finite ∧
    (({S : Finset V | v ∈ S ∧ S.card = ℓ ∧ IsTwoTree G S}.ncard : ℕ) : ℝ) ≤
      (Real.exp 1 * (Δ : ℝ) ^ 2) ^ (ℓ - 1) := by
  classical
  letI : (square G).LocallyFinite := square_locallyFinite G
  have hd : ∀ u, (square G).degree u ≤ Δ^2 := by
    intro u
    exact square_degree_le G Δ hΔ u
  obtain ⟨hfinite, hbound⟩ := CountingLLL.DetCount.lemma_2_5 (square G) (Δ^2) hd v ℓ
  have hsub : {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ IsTwoTree G S} ⊆
      {S : Finset V | v ∈ S ∧ S.card = ℓ ∧ ((square G).induce (S : Set V)).Connected} := by
    intro S hS
    exact ⟨hS.1, hS.2.1, hS.2.2.2⟩
  refine ⟨hfinite.subset hsub, ?_⟩
  have hn := Set.ncard_le_ncard hsub hfinite
  calc
    _ ≤ (({S : Finset V | v ∈ S ∧ S.card = ℓ ∧ ((square G).induce (S : Set V)).Connected}.ncard : ℕ) : ℝ) := by exact_mod_cast hn
    _ ≤ (Real.exp 1 * (Δ : ℝ) ^ 2) ^ (ℓ - 1) := by simpa only [Nat.cast_pow] using hbound
