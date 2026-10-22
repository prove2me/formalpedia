-- Prove2me | solution 3 for GDGen3.certificate_identity_general
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:54:10.026316+00:00
-- url     : https://prove2.me/submissions/e8207d6e-4fc4-417f-963f-5d1370f522d2

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_internal_reduction
import Theorems.Thm_GDGen3_symmetric_square_telescope

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ)
    (hP : ∀ i j, P i j = P j i) :
    certSum r N ξ f P R = certRhs r N P R X0 := by
  have hin := internal_reduction r N hN ξ hr hr1 hpos h0 hquad hquad7 hpin f P hP
  have hfac : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else 2 * r ^ (2 * N) * ell r ξ N i j * Qv (1 + r) f P i j) =
      r ^ (2 * N) * (2 * ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j) := by
    simp only [mul_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    split_ifs <;> ring
  have ht : ∀ i,
      2 * (1 + r) * r ^ (2 * N) * (-f i + gself (1 + r) R P i - (1 / 2) * P i i)
        + 2 * r ^ (2 * N) * ((1 + r) - M r N) * (f i - (1 / 2) * P i i) =
      -2 * r ^ (2 * N) * M r N * f i + 2 * (1 + r) * r ^ (2 * N) * R i
        - 2 * (1 + r) ^ 2 * r ^ (2 * N) * (∑ j ∈ range i, P i j)
        - r ^ (2 * N) * (2 * (1 + r) - M r N) * P i i := by
    intro i; unfold gself; ring
  have hpow : r ^ (2 * N) * r ^ (-(2 * (N : ℤ))) = 1 := by
    rw [zpow_neg]
    have he : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by simp
    rw [he, zpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hr))
  have hsq := symmetric_square_telescope P hP N
  unfold certSum certRhs
  rw [hfac, hin]
  simp only [ht, gself, sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum,
    sum_const, card_range, nsmul_eq_mul]
  linear_combination -(1 + r) ^ 2 * r ^ (2 * N) * hsq - P N N * hpow


/-! ## Section 3: explicit roots and multiplier positivity -/
