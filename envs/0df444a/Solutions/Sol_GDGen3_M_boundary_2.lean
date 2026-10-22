-- Prove2me | solution 2 for GDGen3.M_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:40:41.906369+00:00
-- url     : https://prove2.me/submissions/7c870630-8073-4ba7-a374-63617643435c

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_M_gap

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r)) : M r N = 1 + r := by
  have he : 1 / r ^ (2 * N) = (1 / r ^ N) ^ 2 := by
    rw [Nat.mul_comm 2 N, pow_mul, div_pow, one_pow]
  have h := M_gap r hr hr1 N hN
  rw [he, hboundary, sub_self, zero_div] at h
  linarith
