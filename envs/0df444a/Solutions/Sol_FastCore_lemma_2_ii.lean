-- Prove2me | solution 1 for FastCore.lemma_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:17:19.057341+00:00
-- url     : https://prove2.me/submissions/0200b0a1-8ba0-4cb0-817a-63d115427500

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsWinnerSet
import Definitions.Def_FastCore_IsMBCC
import Definitions.Def_FastCore_w

set_option autoImplicit false

open FastCore ComplementFreeCA.CFRounding

namespace FastCore.CoreProof

theorem le_w {n m : ℕ} {b : Bids n m} {S : Finset (Fin n)} {x : Fin n → Finset (Fin m)}
    (hx : IsAllocation x) (hS : ∀ i, i ∉ S → x i = ∅) : welfare b x ≤ w b S := by
  classical
  unfold w
  exact Finset.le_sup' (welfare b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hS⟩)

theorem w_le {n m : ℕ} {b : Bids n m} {S : Finset (Fin n)} {c : ℝ}
    (h : ∀ x, IsAllocation x → (∀ i, i ∉ S → x i = ∅) → welfare b x ≤ c) : w b S ≤ c := by
  classical
  unfold w
  apply Finset.sup'_le
  intro x hx
  rw [Finset.mem_filter] at hx
  exact h x hx.2.1 hx.2.2

theorem w_attained {n m : ℕ} (b : Bids n m) (S : Finset (Fin n)) :
    ∃ x, IsAllocation x ∧ (∀ i, i ∉ S → x i = ∅) ∧ welfare b x = w b S := by
  classical
  unfold w
  generalize_proofs H
  obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup' H (welfare b)
  rw [Finset.mem_filter] at hx
  exact ⟨x, hx.2.1, hx.2.2, hxeq.symm⟩

theorem sum_pi_eq {n : ℕ} (S : Finset (Fin n)) (π : Fin n → ℝ) :
    ∑ i ∈ S, π i = ∑ i, (if i ∈ S then π i else 0) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Every coalition value is bounded by the truncated welfare (needs `π ≥ 0`). -/
theorem partB {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (S : Finset (Fin n)) :
    w b S - ∑ i ∈ S, π i ≤ w (trunc b π) Finset.univ := by
  have : w b S ≤ w (trunc b π) Finset.univ + ∑ i ∈ S, π i := by
    apply w_le
    intro x hx hS
    have h1 : welfare b x - ∑ i ∈ S, π i ≤ welfare (trunc b π) x := by
      rw [sum_pi_eq, welfare, welfare, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i _
      simp only [trunc]
      by_cases hi : i ∈ S
      · rw [if_pos hi]
        exact le_max_left _ _
      · rw [if_neg hi, hS i hi, hb.1 i, sub_zero]
        exact le_max_right _ _
    have h2 : welfare (trunc b π) x ≤ w (trunc b π) Finset.univ :=
      le_w hx (fun i hi => absurd (Finset.mem_univ i) hi)
    linarith
  linarith

/-- The truncated welfare of an allocation is a coalition value. -/
theorem trunc_bound {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) (π : Fin n → ℝ)
    (x : Fin n → Finset (Fin m)) (hx : IsAllocation x) :
    ∃ S0 : Finset (Fin n), welfare (trunc b π) x ≤ w b S0 - ∑ i ∈ S0, π i := by
  classical
  let S0 := Finset.univ.filter (fun i => 0 < b i (x i) - π i)
  let x' : Fin n → Finset (Fin m) := fun i => if i ∈ S0 then x i else ∅
  have hsub : ∀ i, x' i ⊆ x i := by
    intro i
    simp only [x']
    split_ifs
    · exact le_rfl
    · exact Finset.empty_subset _
  have hx' : IsAllocation x' := fun i i' hii' =>
    Finset.disjoint_of_subset_left (hsub i) (Finset.disjoint_of_subset_right (hsub i') (hx i i' hii'))
  have hsupp : ∀ i, i ∉ S0 → x' i = ∅ := fun i hi => by simp only [x', if_neg hi]
  have e1 : welfare (trunc b π) x = welfare b x' - ∑ i ∈ S0, π i := by
    rw [sum_pi_eq, welfare, welfare, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [trunc, x']
    by_cases hi : i ∈ S0
    · rw [if_pos hi, if_pos hi]
      exact max_eq_left (le_of_lt (Finset.mem_filter.mp hi).2)
    · rw [if_neg hi, if_neg hi, hb.1 i]
      have : ¬ 0 < b i (x i) - π i := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [max_eq_right (not_lt.mp this)]
      ring
  exact ⟨S0, by rw [e1]; linarith [le_w (b := b) hx' hsupp]⟩

end FastCore.CoreProof

open FastCore.CoreProof in
theorem solution {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, 0 < π i) (hM : IsMBCC b π S) :
    IsWinnerSet (trunc b π) S := by
  classical
  -- w is monotone in the coalition
  have wmono : ∀ S₁ S₂ : Finset (Fin n), S₁ ⊆ S₂ → w b S₁ ≤ w b S₂ := by
    intro S₁ S₂ h12
    apply w_le
    intro x hx hS1
    exact le_w hx (fun i hi => hS1 i (fun h => hi (h12 h)))
  -- prices outside S are nonnegative
  have hπ : ∀ i, 0 ≤ π i := by
    intro i
    by_cases hi : i ∈ S
    · exact (hS i hi).le
    · have h1 := hM (insert i S)
      have h2 := wmono S (insert i S) (Finset.subset_insert i S)
      rw [Finset.sum_insert hi] at h1
      linarith
  -- a b-optimal allocation of S
  obtain ⟨x, hx, hxS, hxeq⟩ := w_attained b S
  have hW : w (trunc b π) Finset.univ = w b S - ∑ i ∈ S, π i := by
    apply le_antisymm
    · apply w_le
      intro y hy _
      obtain ⟨S0, hS0⟩ := trunc_bound hb π y hy
      exact hS0.trans (hM S0)
    · exact partB hb hπ S
  have hxopt : w b S - ∑ i ∈ S, π i ≤ welfare (trunc b π) x := by
    rw [← hxeq, sum_pi_eq, welfare, welfare, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    simp only [trunc]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact le_max_left _ _
    · rw [if_neg hi, hxS i hi, hb.1 i, sub_zero]
      exact le_max_right _ _
  refine ⟨x, ⟨hx, fun y hy => ?_⟩, ?_⟩
  · have := le_w (b := trunc b π) hy (fun i hi => absurd (Finset.mem_univ i) hi)
    linarith
  · ext i
    simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi hxi
      -- removing i strictly improves the adjusted value
      have hsupp : ∀ j, j ∉ S.erase i → x j = ∅ := by
        intro j hj
        by_cases hji : j = i
        · rw [hji]; exact hxi
        · exact hxS j (fun h => hj (Finset.mem_erase.mpr ⟨hji, h⟩))
      have h1 := le_w (b := b) hx hsupp
      have h2 := hM (S.erase i)
      have h3 := Finset.sum_erase_add S π hi
      have := hS i hi
      linarith
    · intro hxi
      by_contra hi
      exact hxi (hxS i hi)
