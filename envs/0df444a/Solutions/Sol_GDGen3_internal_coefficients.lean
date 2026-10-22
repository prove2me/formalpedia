-- Prove2me | solution 1 for GDGen3.internal_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:12:26.337185+00:00
-- url     : https://prove2.me/submissions/898363d1-89a9-4e59-a023-a407e02f787a

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_suffix_indicator
import Theorems.Thm_GDGen3_symmetric_sum_diagonal
import Theorems.Thm_GDGen3_weighted_ginner
import Theorems.Thm_GDGen3_mixed_coeff_cancel
import Theorems.Thm_GDGen3_total_sub_suffix
import Theorems.Thm_GDGen3_weighted_function_values
import Theorems.Thm_GDGen3_weighted_squares

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j) =
    ∑ i ∈ range (N + 1), (2 * d r ξ N i * f i
      + (2 * (1 + r) * V r ξ N i - (∑ j ∈ range (N + 1),
          (ell r ξ N i j + ell r ξ N j i)) + 2 * ell r ξ N i i) * P i i) := by
  let L := ell r ξ N
  let B := fun j k => L j k - (1 + r) *
    ((if k < j then ∑ i ∈ range (N + 1), L i j else 0)
      - ∑ i ∈ range (N + 1), if k < i then L i j else 0)
  have hb : ∀ i j, i ≤ N → j ≤ N → i ≠ j → B i j + B j i = 0 := by
    suffices hs : ∀ i j, i < j → j ≤ N → B i j + B j i = 0 by
      intro i j hi hj hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hs i j h hj
      · rw [add_comm]; exact hs j i h hi
    intro i j hij hj
    have hi : i ≤ N := by omega
    simp only [B, if_pos hij, if_neg (by omega : ¬j < i), zero_sub, mul_neg, sub_neg_eq_add]
    rw [total_sub_suffix (fun a => L a j) N i hi,
      sum_suffix_indicator (fun a => L a i) N j]
    have hc := mixed_coeff_cancel r ξ N i j hij hj
    dsimp [L] at *
    linear_combination hc
  have hdiag : ∀ i, B i i = L i i + (1 + r) * V r ξ N i := by
    intro i
    simp only [B, lt_self_iff_false, if_false, zero_sub, mul_neg, sub_neg_eq_add]
    rw [sum_suffix_indicator]
    rfl
  have hz := symmetric_sum_diagonal B P N hP hb
  simp_rw [hdiag] at hz
  have hg := weighted_ginner (1 + r) N L P
  have hmix : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      L i j * P i j) - (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      L i j * ginner (1 + r) P i j) =
      ∑ i ∈ range (N + 1), (L i i + (1 + r) * V r ξ N i) * P i i := by
    rw [hg, ← hz]
    simp only [B, sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]
  have hq : ∀ i j, (if i = j then 0 else L i j * Qv (1 + r) f P i j)
      = L i j * Qv (1 + r) f P i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Qv, ginner, sub_self, mul_zero]
      ring_nf
      simp
    · simp [hij]
  have he : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * Qv (1 + r) f P i j) =
      (∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j - L j i)) * f i)
      - (1 / 2) * (∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j + L j i)) * P i i)
      + (∑ i ∈ range (N + 1), (L i i + (1 + r) * V r ξ N i) * P i i) := by
    have ht : ∀ i j, L i j * Qv (1 + r) f P i j =
        L i j * (f i - f j) - (1 / 2) * (L i j * (P i i + P j j))
        + L i j * P i j - L i j * ginner (1 + r) P i j := by
      intro i j; unfold Qv; ring
    simp only [ht, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [weighted_function_values, weighted_squares]
    simp only [sum_sub_distrib, sum_add_distrib]
    linear_combination hmix
  change 2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
    if i = j then 0 else L i j * Qv (1 + r) f P i j) = _
  simp_rw [hq]
  rw [he]
  simp only [d]
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro i hi
  dsimp [L]
  ring
