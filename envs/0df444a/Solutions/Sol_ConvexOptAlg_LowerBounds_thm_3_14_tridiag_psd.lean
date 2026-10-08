-- Prove2me | solution 1 for ConvexOptAlg.LowerBounds.thm_3_14_tridiag_psd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:52:03.13129+00:00
-- url     : https://prove2.me/submissions/5c699948-2f5d-46de-9fff-e706b4b6d45b

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace Cbf08400Aux

open Finset

def tT (k j l : ℕ) : ℝ :=
  (if l = j ∧ j < k then 2 else 0) + (if l = j + 1 ∧ j + 1 < k then -1 else 0)
    + (if j = l + 1 ∧ j < k then -1 else 0)

lemma sum_filter_lt (n k : ℕ) (hkn : k ≤ n) (a : ℕ → ℝ) :
    ∑ j ∈ range n, (if j < k then a j else 0) = ∑ j ∈ range k, a j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

lemma sum_filter_lt' (n k : ℕ) (hkn : k ≤ n) (a : ℕ → ℝ) :
    ∑ j ∈ range n, (if j + 1 < k then a j else 0) = ∑ j ∈ range (k - 1), a j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; omega

lemma double_sum (n k : ℕ) (hkn : k ≤ n) (g : ℕ → ℝ) :
    ∑ j ∈ range n, ∑ l ∈ range n, g j * tT k j l * g l
      = 2 * ∑ j ∈ range k, g j ^ 2 - 2 * ∑ j ∈ range (k - 1), g j * g (j + 1) := by
  simp only [tT, mul_add, add_mul, Finset.sum_add_distrib]
  have P1 : ∑ j ∈ range n, ∑ l ∈ range n, g j * (if l = j ∧ j < k then (2:ℝ) else 0) * g l
      = 2 * ∑ j ∈ range k, g j ^ 2 := by
    have h : ∀ j ∈ range n, ∑ l ∈ range n, g j * (if l = j ∧ j < k then (2:ℝ) else 0) * g l
        = if j < k then 2 * g j ^ 2 else 0 := by
      intro j hj
      rw [Finset.sum_eq_single j]
      · by_cases hjk : j < k <;> simp [hjk] <;> ring1
      · intro b _ hb; simp [hb]
      · intro h; exact absurd hj h
    rw [Finset.sum_congr rfl h, sum_filter_lt n k hkn, Finset.mul_sum]
  have P2 : ∑ j ∈ range n, ∑ l ∈ range n,
        g j * (if l = j + 1 ∧ j + 1 < k then (-1:ℝ) else 0) * g l
      = - ∑ j ∈ range (k - 1), g j * g (j + 1) := by
    have h : ∀ j ∈ range n, ∑ l ∈ range n,
          g j * (if l = j + 1 ∧ j + 1 < k then (-1:ℝ) else 0) * g l
        = if j + 1 < k then -(g j * g (j + 1)) else 0 := by
      intro j hj
      rw [Finset.sum_eq_single (j + 1)]
      · by_cases hjk : j + 1 < k <;> simp [hjk] <;> ring1
      · intro b _ hb; simp [hb]
      · intro h
        simp only [mem_range] at h
        have : ¬ (j + 1 < k) := by omega
        simp [this]
    rw [Finset.sum_congr rfl h, sum_filter_lt' n k hkn, Finset.sum_neg_distrib]
  have P3 : ∑ j ∈ range n, ∑ l ∈ range n,
        g j * (if j = l + 1 ∧ j < k then (-1:ℝ) else 0) * g l
      = - ∑ j ∈ range (k - 1), g j * g (j + 1) := by
    rw [Finset.sum_comm]
    have h : ∀ l ∈ range n, ∑ j ∈ range n,
          g j * (if j = l + 1 ∧ j < k then (-1:ℝ) else 0) * g l
        = if l + 1 < k then -(g l * g (l + 1)) else 0 := by
      intro l hl
      rw [Finset.sum_eq_single (l + 1)]
      · by_cases hjk : l + 1 < k <;> simp [hjk] <;> ring1
      · intro b _ hb; simp [hb]
      · intro h
        simp only [mem_range] at h
        have : ¬ (l + 1 < k) := by omega
        simp [this]
    rw [Finset.sum_congr rfl h, sum_filter_lt' n k hkn, Finset.sum_neg_distrib]
  rw [P1, P2, P3]; ring

lemma sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Icc 1 m, f i = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma ident_minus (g : ℕ → ℝ) (m : ℕ) :
    2 * ∑ i ∈ Icc 1 (m + 1), g i ^ 2 - 2 * ∑ i ∈ Icc 1 m, g i * g (i + 1)
      = g 1 ^ 2 + g (m + 1) ^ 2 + ∑ i ∈ Icc 1 m, (g i - g (i + 1)) ^ 2 := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1) (fun i => g i ^ 2),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => g i * g (i + 1)),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => (g i - g (i + 1)) ^ 2)]
    linear_combination ih

lemma ident_plus (g : ℕ → ℝ) (m : ℕ) :
    2 * ∑ i ∈ Icc 1 (m + 1), g i ^ 2 + 2 * ∑ i ∈ Icc 1 m, g i * g (i + 1)
      = g 1 ^ 2 + g (m + 1) ^ 2 + ∑ i ∈ Icc 1 m, (g i + g (i + 1)) ^ 2 := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1) (fun i => g i ^ 2),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => g i * g (i + 1)),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) (fun i => (g i + g (i + 1)) ^ 2)]
    linear_combination ih

open ConvexOptAlg.LowerBounds in
lemma ofLp_eq_coord {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
    x.ofLp a = coord x ((a : ℕ) + 1) := by
  simp [coord, a.isLt]

open ConvexOptAlg.LowerBounds in
lemma tridiag_eq (n k : ℕ) (a b : Fin n) : tridiag n k a b = tT k a b := by
  simp only [tridiag, Matrix.of_apply, tT]
  split_ifs <;> first | (exfalso; omega) | norm_num

open ConvexOptAlg.LowerBounds in
lemma quad_eq (n k : ℕ) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    quadForm (tridiag n k) x
      = 2 * ∑ i ∈ Icc 1 k, coord x i ^ 2
          - 2 * ∑ i ∈ Icc 1 (k - 1), coord x i * coord x (i + 1) := by
  have e : quadForm (tridiag n k) x = ∑ j ∈ range n, ∑ l ∈ range n,
      coord x (j + 1) * tT k j l * coord x (l + 1) := by
    simp only [quadForm, dotProduct, Matrix.mulVec, ofLp_eq_coord, tridiag_eq, Finset.mul_sum]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [e, double_sum n k hkn (fun j => coord x (j + 1)), sum_Icc_shift, sum_Icc_shift]

open ConvexOptAlg.LowerBounds in
lemma norm_sq_eq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i ∈ Icc 1 n, coord x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity)),
    sum_Icc_shift, Finset.sum_range (fun j => coord x (j + 1) ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Real.norm_eq_abs, sq_abs, ← ofLp_eq_coord]

end Cbf08400Aux

open Cbf08400Aux in
open ConvexOptAlg.LowerBounds in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (tridiag n k).IsSymm ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        quadForm (tridiag n k) x =
            2 * ∑ i ∈ Finset.Icc 1 k, coord x i ^ 2
              - 2 * ∑ i ∈ Finset.Icc 1 (k - 1), coord x i * coord x (i + 1) ∧
          2 * ∑ i ∈ Finset.Icc 1 k, coord x i ^ 2
              - 2 * ∑ i ∈ Finset.Icc 1 (k - 1), coord x i * coord x (i + 1) =
            coord x 1 ^ 2 + coord x k ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - 1), (coord x i - coord x (i + 1)) ^ 2 ∧
          0 ≤ quadForm (tridiag n k) x ∧ quadForm (tridiag n k) x ≤ 4 * ‖x‖ ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, tridiag, Matrix.of_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  · have hq := quad_eq n (m + 1) hkn x
    simp only [Nat.add_sub_cancel] at hq
    have h2 := ident_minus (coord x) m
    have h3 := ident_plus (coord x) m
    have hn := norm_sq_eq n x
    have hsub : ∑ i ∈ Finset.Icc 1 (m + 1), coord x i ^ 2 ≤ ∑ i ∈ Finset.Icc 1 n, coord x i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hkn)
        (fun _ _ _ => by positivity)
    have hs1 : 0 ≤ ∑ i ∈ Finset.Icc 1 m, (coord x i - coord x (i + 1)) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hs2 : 0 ≤ ∑ i ∈ Finset.Icc 1 m, (coord x i + coord x (i + 1)) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    refine ⟨hq, h2, ?_, ?_⟩
    · rw [hq, h2]; positivity
    · rw [hq, hn]
      nlinarith [sq_nonneg (coord x 1), sq_nonneg (coord x (m + 1))]
