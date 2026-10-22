-- Prove2me | solution 2 for GDGen3.small_step_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T12:05:57.715601+00:00
-- url     : https://prove2.me/submissions/20f6d53c-3e86-4102-b7d5-be1f98373be3

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_small_history_nonneg
import Theorems.Thm_GDGen3_small_step_identity

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (h : ℝ) (hh : 0 < h) (hha : h ≤ 1 + r)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 XN : ℝ)
    (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv h f P i j)
    (hdiff : ∀ i j, i ≤ N → j ≤ N → 0 ≤ P i i + P j j - 2 * P i j)
    (hstar : ∀ i, i < N → 0 ≤ -f i + gself h R P i - (1 / 2) * P i i)
    (hfN : (1 / 2) * P N N ≤ f N) (hXN : P N N ≤ XN)
    (htrajectory : XN = X0 - 2 * h * (∑ i ∈ range N, R i)
      + h ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j)) :
    (1 + (N : ℝ) * h) ^ 2 * P N N ≤ X0 := by
  have hk := small_history_nonneg r hr hr1 N hN hboundary h hh hha f P hP hQ hdiff
  have hs : 0 ≤ ∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i) := by
    apply sum_nonneg; intro i hi; exact hstar i (mem_range.mp hi)
  have he := small_step_identity N h f P R X0 XN hP htrajectory
  have hl : 0 ≤ h * smallK N h f (fun i => P i i) +
      2 * h * (∑ i ∈ range N, (-f i + gself h R P i - (1 / 2) * P i i)) := by positivity
  have hf := mul_le_mul_of_nonneg_left hfN (show 0 ≤ 2 * (N : ℝ) * h by positivity)
  nlinarith [he, hl, hf]
