-- Prove2me | solution 1 for ConvexOptAlg.LowerBounds.thm_3_14_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:54:13.714984+00:00
-- url     : https://prove2.me/submissions/af3754a2-851e-445d-8c55-fb79335b1d27

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

lemma p13184497_icc_range (k : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 k, f i = ∑ j ∈ Finset.range k, f (j + 1) := by
  induction k with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma p13184497_sq_sum (k : ℕ) :
    ∑ j ∈ Finset.range k, ((j : ℝ) + 1) ^ 2 = (k : ℝ) * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

open ConvexOptAlg.LowerBounds in
theorem solution (n k : ℕ) (hkn : k ≤ n) :
    ‖xstarK n k‖ ^ 2 = ∑ i ∈ Finset.Icc 1 k, (1 - (i : ℝ) / ((k : ℝ) + 1)) ^ 2 ∧
      ∑ i ∈ Finset.Icc 1 k, (1 - (i : ℝ) / ((k : ℝ) + 1)) ^ 2 =
        ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) / ((k : ℝ) + 1)) ^ 2 ∧
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) / ((k : ℝ) + 1)) ^ 2 ≤ ((k : ℝ) + 1) / 3 := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_sq_eq]
    simp only [xstarK, Real.norm_eq_abs, sq_abs]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if j + 1 ≤ k then 1 - ((j : ℝ) + 1) / ((k : ℝ) + 1) else 0) ^ 2) n]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [Finset.sum_range_add, p13184497_icc_range]
    have h0 : ∑ x ∈ Finset.range d,
        (if k + x + 1 ≤ k then 1 - ((((k + x : ℕ)) : ℝ) + 1) / ((k : ℝ) + 1) else 0) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg (by omega)]; simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [if_pos (by omega)]
    push_cast; ring
  · rw [p13184497_icc_range, p13184497_icc_range]
    rw [← Finset.sum_range_reflect (fun j : ℕ => (((j + 1 : ℕ) : ℝ) / ((k : ℝ) + 1)) ^ 2) k]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have : ((k - 1 - x + 1 : ℕ) : ℝ) = (k : ℝ) - x := by
      rw [show k - 1 - x + 1 = k - x by omega, Nat.cast_sub hx.le]
    rw [this]
    field_simp
    push_cast; ring
  · rw [p13184497_icc_range]
    have : ∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / ((k : ℝ) + 1)) ^ 2
        = (∑ j ∈ Finset.range k, ((j : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      push_cast; rw [div_pow]
    rw [this, p13184497_sq_sum, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith [hk]
