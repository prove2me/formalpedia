-- Prove2me | solution 1 for ExAnteExPost.RPS.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:46:07.9038+00:00
-- url     : https://prove2.me/submissions/b2643c32-b1f5-4c57-a7c5-dcdabedf518c

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

open Finset ExAnteExPost.RPS

set_option linter.unusedSectionVars false

namespace RPSBvN

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

lemma perm_apply {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) (a b : ι) :
    σ.permMatrix ℝ a b = if σ a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

/-- The doubly stochastic completion of `X`, indexed by agents and goods. -/
noncomputable def Y (X : FracAlloc N G) : Matrix (N ⊕ G) (N ⊕ G) ℝ
  | .inl i, .inr g => X i g
  | .inr g, .inl i => X i g
  | .inl i, .inl i' => if i = i' then 1 - ∑ g, X i g else 0
  | .inr g, .inr g' => if g = g' then 1 - ∑ i, X i g else 0

lemma Y_ds (X : FracAlloc N G) (hX : BvNInput X) : Y X ∈ doublyStochastic ℝ (N ⊕ G) := by
  obtain ⟨h1, h2, h3⟩ := hX
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | g) (i' | g') <;> simp only [Y]
    · split_ifs <;> linarith [h2 i]
    · exact (h1 i g').1
    · exact (h1 i' g).1
    · split_ifs <;> linarith [h3 g]
  · rintro (i | g)
    · rw [Fintype.sum_sum_type]; simp [Y]
    · rw [Fintype.sum_sum_type]; simp [Y]
  · rintro (i | g)
    · rw [Fintype.sum_sum_type]; simp [Y]
    · rw [Fintype.sum_sum_type]; simp [Y]

/-- The integral allocation read off a permutation: agent `i` gets `g` iff `σ (inl i) = inr g`. -/
def alloc (σ : Equiv.Perm (N ⊕ G)) : IntAlloc N G :=
  fun i => univ.filter fun g => σ (.inl i) = .inr g

lemma card_alloc_le (σ : Equiv.Perm (N ⊕ G)) (i : N) : (alloc σ i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [alloc, mem_filter, mem_univ, true_and] at ha hb
  rw [ha] at hb; exact Sum.inr_injective hb

lemma card_holders_le (σ : Equiv.Perm (N ⊕ G)) (g : G) : (holders (alloc σ) g).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [holders, alloc, mem_filter, mem_univ, true_and] at ha hb
  rw [← hb] at ha; exact Sum.inl_injective (σ.injective ha)

theorem bvn (X : FracAlloc N G) (hX : BvNInput X) : ∃ d : Decomp N G, IsBvNDecomp X d := by
  obtain ⟨w, hw0, hw1, hwY⟩ := exists_eq_sum_perm_of_mem_doublyStochastic (Y_ds X hX)
  have hent : ∀ a b, ∑ σ, w σ * (if σ a = b then 1 else 0) = Y X a b := by
    intro a b
    rw [← hwY]
    simp [Matrix.sum_apply, perm_apply]
  -- positive-weight permutations avoid the zero entries of `Y`
  have hzero : ∀ σ, 0 < w σ → ∀ a b, Y X a b = 0 → σ a ≠ b := by
    intro σ hσ a b hab hσab
    have h := hent a b
    rw [hab] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => mul_nonneg (hw0 τ)
      (by split_ifs <;> norm_num))).mp h σ (mem_univ σ)
    rw [if_pos hσab, mul_one] at this; linarith
  set S := univ.filter fun σ : Equiv.Perm (N ⊕ G) => 0 < w σ
  let e : Fin S.card ≃ S := S.equivFin.symm
  refine ⟨⟨S.card, fun k => w (e k), fun k => alloc (e k : Equiv.Perm (N ⊕ G))⟩, ?_⟩
  have hsumS : ∀ f : Equiv.Perm (N ⊕ G) → ℝ, (∀ σ, w σ = 0 → f σ = 0) →
      ∑ k : Fin S.card, f (e k) = ∑ σ, f σ := by
    intro f hf
    rw [Equiv.sum_comp e (fun s : S => f s), Finset.sum_coe_sort S f]
    apply Finset.sum_subset (subset_univ _)
    intro σ _ hσ
    apply hf
    simp only [S, mem_filter, mem_univ, true_and, not_lt] at hσ
    exact le_antisymm hσ (hw0 σ)
  have hpos : ∀ k : Fin S.card, 0 < w (e k) := by
    intro k; have := (e k).2; simp only [S, mem_filter, mem_univ, true_and] at this; exact this
  obtain ⟨h1, h2, h3⟩ := hX
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨hw0 _, ?_⟩
    rw [← hw1]
    exact Finset.single_le_sum (fun σ _ => hw0 σ) (mem_univ _)
  · simp only; rw [hsumS w (fun σ h => h), hw1]
  · intro i g
    simp only
    rw [hsumS (fun σ => w σ * toFrac (alloc σ) i g) (fun σ h => by simp [h])]
    have := hent (.inl i) (.inr g)
    simp only [Y] at this
    rw [← this]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [toFrac, alloc]
  · intro k i
    simp only
    set σ : Equiv.Perm (N ⊕ G) := (e k : Equiv.Perm (N ⊕ G))
    have hσ := hpos k
    have hc := card_alloc_le σ i
    have hr0 : 0 ≤ ∑ g, X i g := Finset.sum_nonneg fun g _ => (h1 i g).1
    by_cases hr1 : ∑ g, X i g = 1
    · -- the slack entries in row `inl i` vanish, so `σ (inl i)` is a good
      have : ∃ g, σ (.inl i) = .inr g := by
        rcases hσi : σ (.inl i) with i' | g
        · exfalso
          refine hzero σ hσ (.inl i) (.inl i') ?_ hσi
          simp only [Y]; split_ifs <;> linarith
        · exact ⟨g, rfl⟩
      obtain ⟨g, hg⟩ := this
      have : 0 < (alloc σ i).card :=
        Finset.card_pos.mpr ⟨g, by simp [alloc, hg]⟩
      rw [hr1, Int.floor_one, Int.ceil_one]; omega
    · by_cases hrz : ∑ g, X i g = 0
      · have hall : ∀ g, X i g = 0 :=
          fun g => (Finset.sum_eq_zero_iff_of_nonneg fun g _ => (h1 i g).1).mp hrz g (mem_univ g)
        have : alloc σ i = ∅ := by
          ext g
          simp only [alloc, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact hzero σ hσ (.inl i) (.inr g) (by simp [Y, hall])
        rw [this, hrz]; simp
      · have hlt : ∑ g, X i g < 1 := lt_of_le_of_ne (h2 i) hr1
        have hgt : 0 < ∑ g, X i g := lt_of_le_of_ne hr0 (Ne.symm hrz)
        have hf : ⌊∑ g, X i g⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hr0, hlt⟩
        have hcl : ⌈∑ g, X i g⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by norm_num [hgt], by norm_num [hlt.le]⟩
        rw [hf, hcl]; omega
  · intro k g
    simp only
    set σ : Equiv.Perm (N ⊕ G) := (e k : Equiv.Perm (N ⊕ G))
    have hσ := hpos k
    have hc := card_holders_le σ g
    have hr0 : 0 ≤ ∑ i, X i g := Finset.sum_nonneg fun i _ => (h1 i g).1
    by_cases hr1 : ∑ i, X i g = 1
    · have : ∃ i, σ (.inl i) = .inr g := by
        rcases hσi : σ.symm (.inr g) with i | g'
        · exact ⟨i, by rw [← hσi]; simp⟩
        · exfalso
          refine hzero σ hσ (.inr g') (.inr g) ?_ (by rw [← hσi]; simp)
          simp only [Y]; split_ifs with hgg
          · subst hgg; linarith
          · rfl
      obtain ⟨i, hi⟩ := this
      have : 0 < (holders (alloc σ) g).card :=
        Finset.card_pos.mpr ⟨i, by simp [holders, alloc, hi]⟩
      rw [hr1, Int.floor_one, Int.ceil_one]; omega
    · by_cases hrz : ∑ i, X i g = 0
      · have hall : ∀ i, X i g = 0 :=
          fun i => (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (h1 i g).1).mp hrz i (mem_univ i)
        have : holders (alloc σ) g = ∅ := by
          ext i
          simp only [holders, alloc, mem_filter, mem_univ, true_and, Finset.notMem_empty,
            iff_false]
          exact hzero σ hσ (.inl i) (.inr g) (by simp [Y, hall])
        rw [this, hrz]; simp
      · have hlt : ∑ i, X i g < 1 := lt_of_le_of_ne (h3 g) hr1
        have hgt : 0 < ∑ i, X i g := lt_of_le_of_ne hr0 (Ne.symm hrz)
        have hf : ⌊∑ i, X i g⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hr0, hlt⟩
        have hcl : ⌈∑ i, X i g⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by norm_num [hgt], by norm_num [hlt.le]⟩
        rw [hf, hcl]; omega

end RPSBvN

theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]
    (X : FracAlloc N G) (hX : BvNInput X) :
    ∃ d : Decomp N G, IsBvNDecomp X d :=
  RPSBvN.bvn X hX
