-- Prove2me | solution 1 for GDGen3.inverse_power_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:42:56.783135+00:00
-- url     : https://prove2.me/submissions/8925d96f-ce2e-4ca6-987d-cd649080eaf6

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (N : ℕ)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r)) :
    r ^ (-(2 * (N : ℤ))) = (1 + (N : ℝ) * (1 + r)) ^ 2 := by
  rw [zpow_neg]
  have he : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by simp
  rw [he, zpow_natCast, Nat.mul_comm 2 N, pow_mul]
  have hd : ((r ^ N) ^ 2)⁻¹ = (1 / r ^ N) ^ 2 := by rw [div_pow, one_pow, one_div]
  rw [hd, hboundary]
