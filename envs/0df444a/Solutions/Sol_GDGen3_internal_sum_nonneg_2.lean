-- Prove2me | solution 2 for GDGen3.internal_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:59:20.125856+00:00
-- url     : https://prove2.me/submissions/a040e888-d91e-43c8-ade8-910472d7402c

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_ell_root_nonneg

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j) :
    0 ≤ 2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else ell r (rootXi r N) N i j * Qv (1 + r) f P i j) := by
  apply mul_nonneg (by norm_num)
  apply sum_nonneg; intro i hi
  apply sum_nonneg; intro j hj
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij]
    exact mul_nonneg
      (ell_root_nonneg r hr hr1 N i j (by simpa using hi) (by simpa using hj) hij hbranch)
      (hQ i j (by simpa using hi) (by simpa using hj) hij)
