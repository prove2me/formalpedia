-- Prove2me | solution 2 for GDGen3.reference_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:35:17.670261+00:00
-- url     : https://prove2.me/submissions/61339352-03c3-4b58-88a7-0176cb4ed2c8

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pow_slope_strictMono

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    1 / r ^ i < 1 + (i : ℝ) * (1 + r) := by
  have hz : 1 < 1 / r := (lt_div_iff₀ hr).2 (by simpa using hr1)
  have hs := pow_slope_strictMono (1 / r) hz (by omega : i - 1 < N - 1)
  dsimp at hs
  have hN : 1 ≤ N := by omega
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hN] at hs
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
  rw [hci, hcN, div_pow, div_pow, one_pow, one_pow] at hs
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs' := (div_lt_div_iff₀ hip hNp).mp hs
  have hm := mul_le_mul_of_nonneg_left hbranch (le_of_lt hip)
  nlinarith
