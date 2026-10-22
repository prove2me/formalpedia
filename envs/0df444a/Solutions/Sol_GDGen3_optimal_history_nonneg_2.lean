-- Prove2me | solution 2 for GDGen3.optimal_history_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T12:01:18.570143+00:00
-- url     : https://prove2.me/submissions/a5579ae5-1479-4d0a-b125-0e58dad95cdb

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_internal_sum_nonneg
import Theorems.Thm_GDGen3_optimal_history_identity

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j) :
    0 ≤ smallK N (1 + r) f (fun i => P i i) := by
  have hn := internal_sum_nonneg r hr hr1 N (le_of_eq hboundary) f P hQ
  rw [← optimal_history_identity r hr hr1 N hN hboundary f P hP] at hn
  by_contra hk
  have hneg := mul_neg_of_pos_of_neg (show 0 < 1 + r by positivity) (lt_of_not_ge hk)
  linarith
