-- Prove2me | solution 2 for GDGen3.internal_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:49:31.171107+00:00
-- url     : https://prove2.me/submissions/a4847d24-c46e-48f4-93e7-5d76c3826525

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_rV_sub_U
import Theorems.Thm_GDGen3_internal_coefficients
import Theorems.Thm_GDGen3_diagonal_coeff
import Theorems.Thm_GDGen3_flow_at_index
import Theorems.Thm_GDGen3_flow_total
import Theorems.Thm_GDGen3_U_last
import Theorems.Thm_GDGen3_V_last
import Theorems.Thm_GDGen3_pj_zpow

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    2 * Finset.sum (Finset.range (N + 1)) (fun i =>
        Finset.sum (Finset.range (N + 1)) (fun j =>
          if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j))
      = 2 * M r N * Finset.sum (Finset.range N) (fun i => f i - f N)
        + (1 - r ^ 2 - M r N) * Finset.sum (Finset.range N) (fun i => P i i)
        + ((N : ℝ) * M r N - r ^ (-(2 * (N : ℤ))) + 1) * P N N := by
  have hdi : ∀ i, i < N → d r ξ N i = M r N :=
    fun i hi => flow_at_index r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin i hi
  have hsumd : (∑ i ∈ range N, d r ξ N i) = (N : ℝ) * M r N := by
    rw [sum_congr rfl (fun i hi => hdi i (mem_range.mp hi))]
    simp [mul_comm]
  have hdN : d r ξ N N = -(N : ℝ) * M r N := by
    have h := flow_total r ξ N
    rw [sum_range_succ, hsumd] at h
    linarith
  have hterm : ∀ i ∈ range N,
      2 * d r ξ N i * f i + (2 * (1 + r) * V r ξ N i
        - (∑ j ∈ range (N + 1), (ell r ξ N i j + ell r ξ N j i))
        + 2 * ell r ξ N i i) * P i i =
      2 * M r N * f i + (1 - r ^ 2 - M r N) * P i i := by
    intro i hi
    have hiN : i < N := mem_range.mp hi
    rw [diagonal_coeff r ξ N i (by omega), hdi i hiN,
      rV_sub_U r N i hN ξ h0 hpos (ne_of_gt hr) (by omega)]
    ring
  have hlast : 2 * d r ξ N N * f N + (2 * (1 + r) * V r ξ N N
        - (∑ j ∈ range (N + 1), (ell r ξ N N j + ell r ξ N j N))
        + 2 * ell r ξ N N N) * P N N =
      -2 * (N : ℝ) * M r N * f N +
        ((N : ℝ) * M r N - r ^ (-(2 * (N : ℤ))) + 1) * P N N := by
    rw [diagonal_coeff r ξ N N le_rfl, hdN, V_last, U_last r N hN ξ h0 hpos]
    have hp := pj_zpow r (ne_of_gt hr) N
    linear_combination -P N N * hp
  rw [internal_coefficients r ξ N f P hP, sum_range_succ, hlast,
    sum_congr rfl hterm]
  simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const,
    card_range, nsmul_eq_mul]
  ring
