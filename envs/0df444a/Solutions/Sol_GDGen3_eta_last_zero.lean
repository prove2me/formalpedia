-- Prove2me | solution 1 for GDGen3.eta_last_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:49:44.475977+00:00
-- url     : https://prove2.me/submissions/de8ba3ec-02a5-4ae8-a401-a6666c07e2fa

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_quad_eta

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i)
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) :
    eta r N ξ (N - 1) = 0 := by
  by_cases hN1 : N = 1
  · subst N
    have hpne : pj r 1 ≠ 0 := by
      unfold pj
      have hlt : r ^ (2 * 1) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
      exact div_ne_zero (by linarith) (by positivity)
    simp only [eta, Nat.sub_self, h0, zero_add, C, M, PiS, sum_range_succ,
      sum_range_zero, zero_add, Nat.cast_one]
    field_simp [hpne]
    ring
  have h := quad_eta r N ξ hquad (N - 1) (by omega)
  rw [← hpin] at h
  have hlt : r ^ (2 * N) < 1 := by
    have h2 : 2 * N ≠ 0 := by omega
    have hN0 : N ≠ 0 := by omega
    exact pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hpj : pj r N ≠ 0 := by
    simp only [pj]
    exact div_ne_zero (by linarith) (by positivity)
  have hne : pj r N * ξ (N - 1) ≠ 0 := mul_ne_zero hpj (ne_of_gt (hpos (N - 1) (by omega)))
  have h' : pj r N * ξ (N - 1) * (1 + eta r N ξ (N - 1)) = pj r N * ξ (N - 1) := by
    simpa [Nat.sub_add_cancel hN] using h
  have h1 : 1 + eta r N ξ (N - 1) = 1 := by
    apply mul_left_cancel₀ hne
    rw [mul_one]
    exact h'
  linarith
