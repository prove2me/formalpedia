-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.reversible_merging
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:25.575278+00:00
-- url     : https://prove2.me/submissions/2a689db6-1150-42d3-afce-bb55607b266f

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

section
set_option autoImplicit false

namespace FiniteSampleDependence.Dev.Lem31

open FiniteSampleDependence.Rigidity Matrix

lemma mul_mem_simplex {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsColumnStochastic T)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) : T * U ∈ simplex n m := by
  obtain ⟨hT0, hT1⟩ := hT
  obtain ⟨hU0, hU1⟩ := hU
  refine ⟨fun i α => ?_, ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hT0 _ _) (hU0 _ _)
  · unfold tau at hU1 ⊢
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ α, ∑ i, ∑ k, T i k * U k α = ∑ α, ∑ k, ∑ i, T i k * U k α := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_comm
      _ = ∑ α, ∑ k, U k α := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_mul, hT1 k, one_mul]
      _ = ∑ i, ∑ α, U i α := by rw [Finset.sum_comm]
      _ = 1 := hU1

lemma merge_apply {n m : ℕ} (i j : Fin n) (hij : i ≠ j) (U : Matrix (Fin n) (Fin m) ℝ)
    (k : Fin n) (α : Fin m) :
    (mergeMatrix i j * U) k α =
      if k = i then U i α + U j α else if k = j then 0 else U k α := by
  simp only [Matrix.mul_apply, mergeMatrix, Matrix.of_apply]
  by_cases hk : k = i
  · subst hk
    simp only [if_true]
    rw [Finset.sum_eq_add_of_mem k j (Finset.mem_univ _) (Finset.mem_univ _) hij]
    · simp [hij.symm, hij]
    · intro l _ hl
      simp [hl.1, hl.2]
  · by_cases hkj : k = j
    · subst hkj
      simp [hk]
    · simp only [hk, hkj, if_false]
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        simp [hl]
      · simp

lemma merge_cs {n : ℕ} (i j : Fin n) (hij : i ≠ j) : IsColumnStochastic (mergeMatrix i j) := by
  refine ⟨fun k l => ?_, fun l => ?_⟩
  · simp only [mergeMatrix, Matrix.of_apply]
    split_ifs <;> simp
  · simp only [mergeMatrix, Matrix.of_apply]
    by_cases hl : l = i ∨ l = j
    · rw [Finset.sum_eq_single i]
      · simp [hl]
      · intro k _ hk
        rcases hl with rfl | rfl
        · simp [hk, Ne.symm hk]
        · simp [hk]
          intro h e
          exact h e.symm
      · simp
    · push Not at hl
      rw [Finset.sum_eq_single l]
      · simp [hl.1, hl.2]
      · intro k _ hk
        by_cases hki : k = i
        · simp [hki, hl.1, hl.2]
        · by_cases hkj : k = j
          · simp [hkj, hij.symm]
          · simp [hki, hkj, Ne.symm hk]
      · simp

/-- The reverse channel. -/
noncomputable def revT {n : ℕ} (i j : Fin n) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k l =>
    if l = i then (if k = i then a / (a + b) else if k = j then b / (a + b) else 0)
    else if k = l then 1 else 0

lemma revT_cs {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 < a + b) : IsColumnStochastic (revT i j a b) := by
  refine ⟨fun k l => ?_, fun l => ?_⟩
  · simp only [revT, Matrix.of_apply]
    have h1 : 0 ≤ a / (a + b) := by positivity
    have h2 : 0 ≤ b / (a + b) := by positivity
    split_ifs <;> simp [h1, h2]
  · simp only [revT, Matrix.of_apply]
    by_cases hl : l = i
    · subst hl
      rw [Finset.sum_eq_add_of_mem l j (Finset.mem_univ _) (Finset.mem_univ _) hij]
      · simp [hij.symm]
        field_simp
      · intro k _ hk
        simp [hk.1, hk.2]
    · rw [Finset.sum_eq_single l]
      · simp [hl]
      · intro k _ hk
        simp [hl, hk]
      · simp

lemma revT_mul {n m : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) (hs : 0 < a + b)
    (U : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ)
    (hi : ∀ α, U i α = a * v α) (hj : ∀ α, U j α = b * v α) :
    revT i j a b * (mergeMatrix i j * U) = U := by
  ext k α
  simp only [Matrix.mul_apply, revT, Matrix.of_apply, merge_apply i j hij]
  by_cases hk : k = i
  · subst hk
    rw [Finset.sum_eq_single k]
    · simp [hi, hj]
      field_simp
    · intro l _ hl
      simp [hl, Ne.symm hl]
    · simp
  · by_cases hkj : k = j
    · subst hkj
      rw [Finset.sum_eq_add_of_mem i k (Finset.mem_univ _) (Finset.mem_univ _) hij]
      · simp [hi, hj, hk, hij]
        field_simp
      · intro l _ hl
        simp [hl.1, hl.2, hk]
        intro h
        exact absurd h.symm hl.2
    · rw [Finset.sum_eq_single k]
      · simp [hk, hkj]
      · intro l _ hl
        by_cases hli : l = i
        · simp [hli, hk, hkj]
        · simp [hli, hl, Ne.symm hl]
      · simp

end FiniteSampleDependence.Dev.Lem31

namespace FiniteSampleDependence.Rigidity

theorem chk_reversible_merging {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F) (i j : Fin n) (hij : i ≠ j)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) :
    F (mergeMatrix i j * U) ≤ F U ∧
    ∀ (a b : ℝ) (v : Fin m → ℝ), 0 ≤ a → 0 ≤ b → (∀ α, 0 ≤ v α) →
      (∀ α, U i α = a * v α) → (∀ α, U j α = b * v α) →
      F (mergeMatrix i j * U) = F U := by
  have hle : F (mergeMatrix i j * U) ≤ F U :=
    hF U hU _ (Dev.Lem31.merge_cs i j hij)
  refine ⟨hle, fun a b v ha hb _ hi hj => ?_⟩
  apply le_antisymm hle
  have hmem := Dev.Lem31.mul_mem_simplex _ (Dev.Lem31.merge_cs i j hij) U hU
  rcases (add_nonneg ha hb).eq_or_lt with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have : mergeMatrix i j * U = U := by
      ext k α
      rw [Dev.Lem31.merge_apply i j hij]
      by_cases hk : k = i
      · subst hk; simp [hi, hj, ha0, hb0]
      · by_cases hkj : k = j
        · subst hkj; simp [hk, hj, hb0]
        · simp [hk, hkj]
    rw [this]
  · have := hF _ hmem _ (Dev.Lem31.revT_cs i j hij a b ha hb hs)
    rwa [Dev.Lem31.revT_mul i j hij a b hs U v hi hj] at this

end FiniteSampleDependence.Rigidity
end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_reversible_merging := @FiniteSampleDependence.Rigidity.chk_reversible_merging
