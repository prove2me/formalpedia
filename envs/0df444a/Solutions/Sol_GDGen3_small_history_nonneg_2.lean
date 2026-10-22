-- Prove2me | solution 2 for GDGen3.small_history_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T12:04:29.515748+00:00
-- url     : https://prove2.me/submissions/24c2c673-304a-401c-a092-127e5c4f08c7

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_optimal_history_nonneg
import Theorems.Thm_GDGen3_interpolation_scaling
import Theorems.Thm_GDGen3_gradient_square_step
import Theorems.Thm_GDGen3_decreasing_sequence_tail
import Theorems.Thm_GDGen3_scaled_history_identity
import Theorems.Thm_GDGen3_small_history_split

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (h : ℝ) (hh : 0 < h) (hha : h ≤ 1 + r)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv h f P i j)
    (hdiff : ∀ i j, i ≤ N → j ≤ N → 0 ≤ P i i + P j j - 2 * P i j) :
    0 ≤ smallK N h f (fun i => P i i) := by
  let s := h / (1 + r)
  have hs : 0 < s := div_pos hh (by positivity)
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 hha
  have he : h = s * (1 + r) := by dsimp [s]; field_simp
  have hPs : ∀ i j, s ^ 2 * P i j = s ^ 2 * P j i := by intro i j; rw [hP]
  have hQs : ∀ i j, i ≤ N → j ≤ N → i ≠ j →
      0 ≤ Qv (1 + r) (fun i => s * f i) (fun i j => s ^ 2 * P i j) i j := by
    intro i j hi hj hij
    rw [interpolation_scaling (1 + r) s h he]
    exact add_nonneg (mul_nonneg (le_of_lt hs) (hQ i j hi hj hij))
      (mul_nonneg (by positivity) (hdiff i j hi hj))
  have hk := optimal_history_nonneg r hr hr1 N hN hboundary
    (fun i => s * f i) (fun i j => s ^ 2 * P i j) hPs hQs
  rw [scaled_history_identity] at hk
  have hks : 0 ≤ scaledK N (1 + r) s f (fun i => P i i) := by
    by_contra hneg
    have hn := mul_neg_of_pos_of_neg hs (lt_of_not_ge hneg)
    linarith
  have hstep : ∀ i, i < N → P (i + 1) (i + 1) ≤ P i i := by
    intro i hi
    exact gradient_square_step h hh (by linarith) f P hP i
      (hQ i (i + 1) (by omega) (by omega) (by omega))
      (hQ (i + 1) i (by omega) (by omega) (by omega)) (hdiff i (i + 1) (by omega) (by omega))
  have hsum : 0 ≤ (∑ i ∈ range N, P i i) - (N : ℝ) * P N N := by
    have ht : 0 ≤ ∑ i ∈ range N, (P i i - P N N) := by
      apply sum_nonneg; intro i hi
      exact sub_nonneg.mpr (decreasing_sequence_tail (fun i => P i i) N hstep i (le_of_lt (mem_range.mp hi)))
    simpa only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] using ht
  rw [small_history_split N (1 + r) s h he]
  exact add_nonneg hks (mul_nonneg (by linarith) hsum)
