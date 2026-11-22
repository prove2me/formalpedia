-- Prove2me | solution 1 for BooleanIsoperimetry.int_sum_mul_le_of_prefix_le_of_antitone_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:16.752316+00:00
-- url     : https://prove2.me/submissions/2ab6e419-c00c-47f0-83b2-65a2dc41cfeb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (M : ℕ) (u v w : ℕ → ℤ)
    (hpref : ∀ r ≤ M, ∑ i ∈ Finset.range r, v i ≤ ∑ i ∈ Finset.range r, u i)
    (htot : ∑ i ∈ Finset.range M, u i = ∑ i ∈ Finset.range M, v i)
    (_ : ∀ i, i < M → 0 ≤ w i)
    (hwanti : ∀ i, i + 1 < M → w (i + 1) ≤ w i) :
    ∑ i ∈ Finset.range M, w i * v i ≤ ∑ i ∈ Finset.range M, w i * u i := by
  have H : ∑ i ∈ Finset.range M, w i * (u i - v i) ≥ 0 := by
    by_cases hM : M = 0
    · simp [hM]
    have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have h_sum_parts := Finset.sum_range_by_parts (n := M) (f := w) (g := fun i => u i - v i)
    have htot_sub : ∑ i ∈ Finset.range M, (u i - v i) = 0 := by
      rw [Finset.sum_sub_distrib, htot, sub_self]
    rw [htot_sub, smul_zero, zero_sub] at h_sum_parts
    have h_rw : ∀ i, w i * (u i - v i) = w i • (u i - v i) := fun i => rfl
    simp_rw [h_rw]
    rw [h_sum_parts]
    have h_sum_nonpos :
        ∑ i ∈ Finset.range (M - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1),
          (u j - v j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      rw [Finset.mem_range] at hi
      have hw_diff : w (i + 1) - w i ≤ 0 := by
        have : i + 1 < M := by omega
        linarith [hwanti i this]
      have h_S : 0 ≤ ∑ j ∈ Finset.range (i + 1), (u j - v j) := by
        rw [Finset.sum_sub_distrib, sub_nonneg]
        apply hpref (i + 1) (by omega)
      have H_smul : (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), (u j - v j) =
        (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), (u j - v j) := rfl
      rw [H_smul]
      exact mul_nonpos_of_nonpos_of_nonneg hw_diff h_S
    linarith
  have H2 : ∑ i ∈ Finset.range M, w i * u i - ∑ i ∈ Finset.range M, w i * v i ≥ 0 := by
    calc ∑ i ∈ Finset.range M, w i * u i - ∑ i ∈ Finset.range M, w i * v i
      _ = ∑ i ∈ Finset.range M, (w i * u i - w i * v i) := by rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ Finset.range M, w i * (u i - v i) := by { congr; ext i; ring }
      _ ≥ 0 := H
  linarith
end BooleanIsoperimetry
