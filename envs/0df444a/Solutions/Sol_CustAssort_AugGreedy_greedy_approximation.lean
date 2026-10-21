-- Prove2me | solution 1 for CustAssort.AugGreedy.greedy_approximation
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T19:30:44.169373+00:00
-- url     : https://prove2.me/submissions/e9df2daf-31a6-44a8-bccb-b32a8d5dfa6c

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

set_option autoImplicit false

namespace GreedyBound
open CustAssort.AugGreedy

theorem union_bound {α : Type*} [DecidableEq α] (g : Finset α → ℝ)
    (P A : Finset α) (hA : A ⊆ P) (hsub : SubmodularOn g P)
    (d : ℝ) (hd : 0 ≤ d)
    (hgain : ∀ i ∈ P \ A, g (insert i A) - g A ≤ d)
    (T : Finset α) (hT : T ⊆ P) :
    g (A ∪ T) - g A ≤ (T.card : ℝ) * d := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hiP : i ∈ P := hT (Finset.mem_insert_self i T)
    have hTP : T ⊆ P := fun j hj => hT (Finset.mem_insert_of_mem hj)
    have ih' := ih hTP
    rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    have hunion : A ∪ insert i T = insert i (A ∪ T) := by ext; simp
    rw [hunion]
    by_cases hm : i ∈ A ∪ T
    · rw [Finset.insert_eq_of_mem hm]
      nlinarith
    · have hiA : i ∉ A := fun ha => hm (Finset.mem_union_left T ha)
      have hsu := hsub A (A ∪ T) Finset.subset_union_left
        (Finset.union_subset hA hTP) i (Finset.mem_sdiff.mpr ⟨hiP, hm⟩)
      have hg := hgain i (Finset.mem_sdiff.mpr ⟨hiP, hiA⟩)
      nlinarith

theorem reach_bounds {α : Type*} [DecidableEq α] (g : Finset α → ℝ)
    (P : Finset α) (k : ℕ) (D : Finset α) (hD : GreedyReach g P k D) :
    D ⊆ P ∧ D.card ≤ k := by
  induction hD with
  | nil => simp
  | @step D i _ hcard hi _ ih =>
    exact ⟨Finset.insert_subset (Finset.mem_sdiff.mp hi).1 ih.1,
      by rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hi).2]; omega⟩

theorem residual {α : Type*} [DecidableEq α] (g : Finset α → ℝ)
    (P : Finset α) (k : ℕ) (hk : 0 < k)
    (hmono : ∀ A B : Finset α, A ⊆ B → B ⊆ P → g A ≤ g B)
    (hsub : SubmodularOn g P) (hzero : 0 ≤ g ∅)
    (S : Finset α) (hS : S ⊆ P) (hSk : S.card ≤ k)
    (D : Finset α) (hD : GreedyReach g P k D) :
    g S - g D ≤ (1 - 1 / (k : ℝ)) ^ D.card * g S := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 ≤ 1 - 1 / (k : ℝ) := by
    have := (div_le_one hkR).2 hk1
    linarith
  induction hD with
  | nil => simpa using hzero
  | @step D i hr hcard hi hmax ih =>
    have hDP := (reach_bounds g P k D hr).1
    have hiP := (Finset.mem_sdiff.mp hi).1
    have hiD := (Finset.mem_sdiff.mp hi).2
    have hgain0 : 0 ≤ g (insert i D) - g D :=
      sub_nonneg.mpr (hmono D (insert i D) (Finset.subset_insert i D)
        (Finset.insert_subset hiP hDP))
    have hub := union_bound g P D hDP hsub (g (insert i D) - g D) hgain0
      (by intro j hj; exact sub_le_sub_right (hmax j hj) _) S hS
    have hSunion := hmono S (D ∪ S) Finset.subset_union_right
      (Finset.union_subset hDP hS)
    have hcount : (S.card : ℝ) ≤ k := by exact_mod_cast hSk
    have hgap : g S - g D ≤ (k : ℝ) * (g (insert i D) - g D) := by
      have := mul_le_mul_of_nonneg_right hcount hgain0
      linarith
    have hdiv : (g S - g D) / (k : ℝ) ≤ g (insert i D) - g D :=
      (div_le_iff₀ hkR).2 (by nlinarith [hgap])
    have hstep : g S - g (insert i D) ≤
        (1 - 1 / (k : ℝ)) * (g S - g D) := by
      calc
        g S - g (insert i D) = (g S - g D) - (g (insert i D) - g D) := by ring
        _ ≤ (g S - g D) - (g S - g D) / (k : ℝ) := sub_le_sub_left hdiv _
        _ = (1 - 1 / (k : ℝ)) * (g S - g D) := by ring
    rw [Finset.card_insert_of_notMem hiD, pow_succ]
    have := mul_le_mul_of_nonneg_left ih hq
    nlinarith [hstep]

theorem power_bound (k : ℕ) (hk : 0 < k) :
    (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 ≤ 1 - 1 / (k : ℝ) := by
    have := (div_le_one hkR).2 hk1
    linarith
  have hle : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (k : ℝ)))
    linarith
  calc
    (1 - 1 / (k : ℝ)) ^ k ≤ (Real.exp (-(1 / (k : ℝ)))) ^ k :=
      pow_le_pow_left₀ hq hle k
    _ = Real.exp ((k : ℝ) * (-(1 / (k : ℝ)))) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-1) := by congr 1; field_simp

end GreedyBound

open CustAssort.AugGreedy

theorem solution {α : Type*} [DecidableEq α] (g : Finset α → ℝ)
    (P : Finset α) (k : ℕ) (Δ : Finset α)
    (hmono : ∀ A B : Finset α, A ⊆ B → B ⊆ P → g A ≤ g B)
    (hsub : SubmodularOn g P) (hzero : 0 ≤ g ∅)
    (hΔ : IsGreedyOutput g P k Δ) :
    ∀ S : Finset α, S ⊆ P → S.card ≤ k →
      (1 - Real.exp (-1)) * g S ≤ g Δ := by
  intro S hS hSk
  have hbounds := GreedyBound.reach_bounds g P k Δ hΔ.1
  have hS0 : 0 ≤ g S := le_trans hzero (hmono ∅ S (Finset.empty_subset S) hS)
  have hD0 : 0 ≤ g Δ := le_trans hzero (hmono ∅ Δ (Finset.empty_subset Δ) hbounds.1)
  have he : 0 ≤ Real.exp (-1 : ℝ) := (Real.exp_pos _).le
  by_cases hk : k = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    have h0le := hmono ∅ Δ (Finset.empty_subset Δ) hbounds.1
    nlinarith [mul_nonneg he hzero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    by_cases hn : (P \ Δ).Nonempty
    · have hc : Δ.card = k := by
        have hnlt : ¬ Δ.card < k := fun h => hΔ.2 ⟨h, hn⟩
        omega
      have hr := GreedyBound.residual g P k hkpos hmono hsub hzero S hS hSk Δ hΔ.1
      rw [hc] at hr
      have hp := mul_le_mul_of_nonneg_right (GreedyBound.power_bound k hkpos) hS0
      nlinarith
    · have hPD : P ⊆ Δ := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp hn)
      have hle := hmono S Δ (Finset.Subset.trans hS hPD) hbounds.1
      nlinarith [mul_nonneg he hS0]

#print axioms solution
