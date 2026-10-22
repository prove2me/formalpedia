-- Prove2me | solution 2 for GDGen3.certificate_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:59:19.392297+00:00
-- url     : https://prove2.me/submissions/e49a93c8-d8ea-475a-ba51-5d2747554be9

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_M_pos
import Theorems.Thm_GDGen3_M_le_h
import Theorems.Thm_GDGen3_ell_root_nonneg

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j)
    (hstar : ∀ i, i ≤ N → 0 ≤ -f i + gself (1 + r) R P i - (1 / 2) * P i i)
    (hto : ∀ i, i ≤ N → 0 ≤ f i - (1 / 2) * P i i) :
    0 ≤ certSum r N (rootXi r N) f P R := by
  have hm := M_le_h r hr hr1 N hN hbranch
  have hmp := M_pos r hr hr1 N hN
  unfold certSum
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · apply sum_nonneg; intro i hi
        apply sum_nonneg; intro j hj
        by_cases hij : i = j
        · simp [hij]
        · rw [if_neg hij]
          exact mul_nonneg (mul_nonneg (by positivity)
            (ell_root_nonneg r hr hr1 N i j (by simpa using hi) (by simpa using hj) hij hbranch))
            (hQ i j (by simpa using hi) (by simpa using hj) hij)
      · apply sum_nonneg; intro i hi
        have hiN : i ≤ N := le_of_lt (mem_range.mp hi)
        apply add_nonneg
        · exact mul_nonneg (by positivity) (hstar i hiN)
        · exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (hto i hiN)
    · exact mul_nonneg (by positivity) (hstar N le_rfl)
  · exact mul_nonneg (by positivity) (hto N le_rfl)
