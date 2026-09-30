-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.sum_layers_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:45:27.358809+00:00
-- url     : https://prove2.me/submissions/1a85cb30-1c30-4c4a-a310-43be4342d47a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm
open Finset ComplementFreeCA.CFRounding

private theorem rank_strict {n m : ℕ} (σ : Fin n → Finset (Fin m)) (j : Fin m)
    {i i' : Fin n} (hi : j ∈ σ i) (hii' : i < i') :
    (univ.filter fun l => l < i ∧ j ∈ σ l).card < (univ.filter fun l => l < i' ∧ j ∈ σ l).card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hii', hl.2⟩
  · intro he
    have hmem : i ∈ univ.filter fun l => l < i' ∧ j ∈ σ l := by simp [hii', hi]
    rw [← he] at hmem
    simpa using hmem

private theorem rank_bound {n m : ℕ} (σ : Fin n → Finset (Fin m)) (j : Fin m)
    (i : Fin n) (hi : j ∈ σ i) :
    (univ.filter fun l => l < i ∧ j ∈ σ l).card < count σ j := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact hl.2
  · intro he
    have hmem : i ∈ univ.filter fun l => j ∈ σ l := by simp [hi]
    rw [← he] at hmem
    simpa using hmem

private theorem layers_partition {n m : ℕ} (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) :
    (∀ r : ℕ, 1 ≤ r → r ≤ k → IsAllocation (fun i => layer σ i r)) ∧
    (∀ i : Fin n, σ i = (Finset.Icc 1 k).biUnion (fun r => layer σ i r)) ∧
    (∀ (i : Fin n) (r r' : ℕ), 1 ≤ r → 1 ≤ r' → r ≠ r' →
      Disjoint (layer σ i r) (layer σ i r')) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hrk i i' hne
    apply disjoint_left.mpr
    intro j hj hj'
    simp only [layer, mem_filter] at hj hj'
    rcases lt_or_gt_of_ne hne with h | h
    · have := rank_strict σ j hj.1 h
      omega
    · have := rank_strict σ j hj'.1 h
      omega
  · intro i
    ext j
    simp only [mem_biUnion, mem_Icc]
    constructor
    · intro hj
      let q := (univ.filter fun l => l < i ∧ j ∈ σ l).card
      refine ⟨q+1, ⟨by omega, ?_⟩, ?_⟩
      · have h := rank_bound σ j i hj
        have hc := hcount j
        omega
      · simp [layer, hj, q]
    · rintro ⟨r, hr, hj⟩
      exact (mem_filter.mp hj).1
  · intro i r r' hr hr' hne
    apply disjoint_left.mpr
    intro j hj hj'
    simp only [layer, mem_filter] at hj hj'
    omega

private theorem sum_layers {n m : ℕ} (v : Finset (Fin m) → ℝ) (hnorm : IsNormalized v)
    (hsub : IsSubadditive v) (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) (i : Fin n) :
    v (σ i) ≤ ∑ r ∈ Finset.Icc 1 k, v (layer σ i r) := by
  have hgen : ∀ s : Finset ℕ, v (s.biUnion (layer σ i)) ≤ ∑ r ∈ s, v (layer σ i r) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [biUnion_empty, sum_empty] using le_of_eq hnorm
    | @insert r s hr ih =>
      rw [biUnion_insert, sum_insert hr]
      exact (hsub _ _).trans (add_le_add le_rfl ih)
  rw [(layers_partition σ k hcount).2.1 i]
  exact hgen _

theorem solution {n m : ℕ} (v : Finset (Fin m) → ℝ) (hnorm : IsNormalized v)
    (hsub : IsSubadditive v) (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) (i : Fin n) :
    v (σ i) ≤ ∑ r ∈ Finset.Icc 1 k, v (layer σ i r) := sum_layers v hnorm hsub σ k hcount i
