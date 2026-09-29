-- Prove2me | solution 1 for BanditAlgorithm.finite_gap_pull_bound_to_minimax
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T22:27:18.593365+00:00
-- url     : https://prove2.me/submissions/bd1c9ac0-1d05-4d32-80fa-8e7d6bf3b210

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k n : ℕ} [NeZero k]
    (hn : 2 ≤ n) (Δ T : Fin k → ℝ) (C : ℝ)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1)
    (hT : ∀ i, 0 ≤ T i) (hsum : ∑ i, T i = n)
    (hC : 0 ≤ C)
    (hpull : ∀ i, 0 < Δ i →
      T i ≤ C * (1 + Real.log n / Δ i ^ 2)) :
    ∑ i, Δ i * T i ≤
      (1 + 3 * C) * Real.sqrt (k * n * Real.log n) := by
  let L : ℝ := Real.log n
  let q : ℝ := Real.sqrt ((k : ℝ) * L / n)
  let B : ℝ := Real.sqrt ((k : ℝ) * n * L)
  have hnR : (0 : ℝ) < n := by positivity
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hn1R : (1 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by omega : 1 < 2) hn
  have hL : 0 < L := by
    exact Real.log_pos hn1R
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hq_mul_n : q * n = B := by
    dsimp [q, B, L]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    calc
      Real.sqrt ((k : ℝ) * Real.log n / n) * n =
          Real.sqrt ((k : ℝ) * Real.log n / n) * |(n : ℝ)| := by
            rw [abs_of_pos hnR]
      _ = Real.sqrt ((k : ℝ) * Real.log n / n) *
          Real.sqrt ((n : ℝ) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (((k : ℝ) * Real.log n / n) * (n : ℝ) ^ 2) := by
        rw [Real.sqrt_mul (by positivity :
          0 ≤ (k : ℝ) * Real.log n / n)]
      _ = Real.sqrt ((k : ℝ) * n * Real.log n) := by
        congr 1
        field_simp
  have hkL_div_q : (k : ℝ) * L / q = B := by
    have hq2 : q ^ 2 = (k : ℝ) * L / n := by
      dsimp [q]
      rw [Real.sq_sqrt]
      positivity
    have hq2mul : q ^ 2 * n = (k : ℝ) * L := by
      rw [hq2]
      field_simp [ne_of_gt hnR]
    calc
      (k : ℝ) * L / q = q * n := by
        rw [← hq2mul]
        field_simp [ne_of_gt hq]
      _ = B := hq_mul_n
  let S : Finset (Fin k) := Finset.univ.filter (fun i ↦ Δ i ≤ q)
  let G : Finset (Fin k) := Finset.univ.filter (fun i ↦ q < Δ i)
  have hpartition :
      (∑ i, Δ i * T i) =
        (∑ i ∈ S, Δ i * T i) + ∑ i ∈ G, Δ i * T i := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext i
        simp only [S, G, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (iff_true_intro (le_or_gt (Δ i) q)).symm
      · intro i hi
        rfl
    · rw [Finset.disjoint_left]
      intro i hiS hiG
      exact (not_lt_of_ge (Finset.mem_filter.1 hiS).2)
        (Finset.mem_filter.1 hiG).2
  have hsmall : (∑ i ∈ S, Δ i * T i) ≤ B := by
    calc
      (∑ i ∈ S, Δ i * T i) ≤ ∑ i ∈ S, q * T i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (Finset.mem_filter.1 hi).2 (hT i)
      _ ≤ ∑ i, q * T i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro i _ _
        exact mul_nonneg hq.le (hT i)
      _ = q * ∑ i, T i := by rw [Finset.mul_sum]
      _ = q * n := by rw [hsum]
      _ = B := hq_mul_n
  have hlog_two : (1 / 2 : ℝ) ≤ L := by
    dsimp [L]
    have hlog2 : Real.log 2 > (1 / 2 : ℝ) :=
      Real.log_two_gt_d9.trans' (by norm_num)
    exact hlog2.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hlarge_each (i : Fin k) (hi : i ∈ G) :
      Δ i * T i ≤ 3 * C * (L / q) := by
    have hqi : q < Δ i := (Finset.mem_filter.1 hi).2
    have hΔpos : 0 < Δ i := hq.trans hqi
    have hΔle : Δ i ≤ 1 := (hΔ i).2
    have hTbound := hpull i hΔpos
    have hmul :
        Δ i * T i ≤ C * (Δ i + L / Δ i) := by
      calc
        Δ i * T i ≤ Δ i * (C * (1 + L / Δ i ^ 2)) := by
          gcongr
        _ = C * (Δ i + L / Δ i) := by
          field_simp [ne_of_gt hΔpos]
    have hone : (1 : ℝ) ≤ 2 * L / q := by
      have hq_lt_one : q < 1 := hqi.trans_le hΔle
      have : q ≤ 2 * L := by nlinarith
      exact (le_div_iff₀ hq).2 (by simpa using this)
    have hterm : Δ i + L / Δ i ≤ 3 * (L / q) := by
      have hfirst : Δ i ≤ 2 * L / q := hΔle.trans hone
      have hsecond : L / Δ i ≤ L / q := by
        exact div_le_div_of_nonneg_left hL.le hq hqi.le
      calc
        Δ i + L / Δ i ≤ 2 * L / q + L / q := add_le_add hfirst hsecond
        _ = 3 * (L / q) := by ring
    calc
      Δ i * T i ≤ C * (Δ i + L / Δ i) := hmul
      _ ≤ C * (3 * (L / q)) := by gcongr
      _ = 3 * C * (L / q) := by ring
  have hlarge : (∑ i ∈ G, Δ i * T i) ≤ 3 * C * B := by
    calc
      (∑ i ∈ G, Δ i * T i) ≤ ∑ i ∈ G, 3 * C * (L / q) := by
        exact Finset.sum_le_sum fun i hi ↦ hlarge_each i hi
      _ ≤ ∑ _i : Fin k, 3 * C * (L / q) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        intro i _ _
        positivity
      _ = 3 * C * ((k : ℝ) * L / q) := by
        simp
        ring
      _ = 3 * C * B := by rw [hkL_div_q]
  rw [hpartition]
  calc
    (∑ i ∈ S, Δ i * T i) + ∑ i ∈ G, Δ i * T i
        ≤ B + 3 * C * B := add_le_add hsmall hlarge
    _ = (1 + 3 * C) * B := by ring

end BanditAlgorithm
