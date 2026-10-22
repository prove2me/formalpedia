-- Prove2me | solution 1 for FinNetProp.Mitosis.part_I_limited_liability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:04:50.542833+00:00
-- url     : https://prove2.me/submissions/3c95ea31-03af-453b-94a9-696fc709510b

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

open Finset

lemma fnp_relLiab_nonneg (F : FinNet) (i j : ℕ) : 0 ≤ relLiab F i j := by
  unfold relLiab
  split_ifs
  · exact le_rfl
  · exact div_nonneg (F.L_nonneg i j) (Finset.sum_nonneg fun k _ => F.L_nonneg i k)

lemma fnp_rowsum_nonneg (F : FinNet) (i : ℕ) : 0 ≤ ∑ k ∈ F.N, F.L i k :=
  Finset.sum_nonneg fun k _ => F.L_nonneg i k

lemma fnp_L_eq_zero_of_rowsum (F : FinNet) (i j : ℕ) (h : ∑ k ∈ F.N, F.L i k = 0) :
    F.L i j = 0 := by
  by_cases hj : j ∈ F.N
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => F.L_nonneg i k)).1 h j hj
  · exact F.L_out i j (Or.inr hj)

lemma fnp_relLiab_mul (F : FinNet) (i j : ℕ) :
    relLiab F i j * ∑ k ∈ F.N, F.L i k = F.L i j := by
  unfold relLiab
  split_ifs with h
  · simp [h]
  · have hpos : (∑ k ∈ F.N, F.L i k) ≠ 0 := by
      intro h0; exact h (fnp_L_eq_zero_of_rowsum F i j h0)
    field_simp

lemma fnp_relLiab_rowsum (F : FinNet) (i : ℕ) :
    ∑ j ∈ F.N, relLiab F i j = if ∑ k ∈ F.N, F.L i k = 0 then 0 else 1 := by
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro j _
    simp [relLiab, fnp_L_eq_zero_of_rowsum F i j h]
  · have : ∀ j ∈ F.N, relLiab F i j = F.L i j / ∑ k ∈ F.N, F.L i k := by
      intro j _
      unfold relLiab
      split_ifs with hj
      · simp [hj]
      · rfl
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, div_self h]

lemma fnp_relLiab_rowsum_le (F : FinNet) (i : ℕ) : ∑ j ∈ F.N, relLiab F i j ≤ 1 := by
  rw [fnp_relLiab_rowsum]; split_ifs <;> norm_num

lemma fnp_min_eq (F : FinNet) (i j : ℕ) (a : ℝ) :
    min (relLiab F i j * a) (F.L i j) = relLiab F i j * min a (∑ k ∈ F.N, F.L i k) := by
  rw [mul_min_of_nonneg _ _ (fnp_relLiab_nonneg F i j), fnp_relLiab_mul]

lemma fnp_z_nonneg (F : FinNet) (i : ℕ) : 0 ≤ F.z i := by
  by_cases h : i ∈ F.N
  · exact (F.z_pos i h).le
  · exact (F.z_out i h).ge

lemma fnp_rowtotal (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    ∀ i ∈ F.N, ∑ l ∈ F.N, P i l =
      min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
  obtain ⟨⟨hnn, _, _⟩, heq⟩ := hP
  intro i hi
  have h1 : ∀ l ∈ F.N, P i l = relLiab F i l *
      min (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k) := by
    intro l hl; rw [heq i hi l hl, fnp_min_eq]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, fnp_relLiab_rowsum]
  split_ifs with h
  · rw [h, zero_mul]
    have : 0 ≤ F.z i + ∑ k ∈ F.N, P k i :=
      add_nonneg (fnp_z_nonneg F i) (Finset.sum_nonneg fun k _ => hnn k i)
    exact (min_eq_right this).symm
  · rw [one_mul]

theorem fnp_ll (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    ∀ i ∈ F.N, 0 ≤ equity F P i := by
  intro i hi
  have h := fnp_rowtotal F P hP i hi
  unfold equity assetValue
  rw [h]
  have := min_le_left (F.z i + ∑ k ∈ F.N, P k i) (∑ k ∈ F.N, F.L i k)
  linarith

end FinNetProp.Mitosis

theorem solution (F : FinNetProp.Mitosis.FinNet) (P : ℕ → ℕ → ℝ)
    (hP : FinNetProp.Mitosis.IsPropSolution F P) :
    ∀ i ∈ F.N, 0 ≤ FinNetProp.Mitosis.equity F P i :=
  FinNetProp.Mitosis.fnp_ll F P hP
