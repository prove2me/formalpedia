-- Prove2me | solution 2 for GDGen3.M_le_h
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:37:11.052105+00:00
-- url     : https://prove2.me/submissions/ad6cd709-bda9-4c41-93a7-c191e0df1747

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_M_gap

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : M r N ≤ 1 + r := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb : (1 / r ^ N) ^ 2 ≤ (1 + (N : ℝ) * (1 + r)) ^ 2 := by
    have hi : 0 ≤ 1 / r ^ N := by positivity
    nlinarith
  have he : (1 / r ^ N) ^ 2 = 1 / r ^ (2 * N) := by
    rw [Nat.mul_comm 2 N, pow_mul, div_pow, one_pow]
  rw [he] at hb
  have hgap : 0 ≤ (1 + r) - M r N := by
    rw [M_gap r hr hr1 N hN]
    apply div_nonneg (by linarith) (by positivity)
  linarith
