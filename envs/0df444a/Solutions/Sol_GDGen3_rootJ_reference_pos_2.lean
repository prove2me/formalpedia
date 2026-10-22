-- Prove2me | solution 2 for GDGen3.rootJ_reference_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:44:16.588818+00:00
-- url     : https://prove2.me/submissions/d646d3e4-b3ae-4beb-8079-92ffc604b9dd

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_rootE_pos
import Theorems.Thm_GDGen3_rootJ_reference_factor

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    0 < rootJ r (1 + r) (referenceXi r (i - 1)) i := by
  rw [rootJ_reference_factor r hr hr1 i hi]
  have hp : 0 < r ^ i := pow_pos hr i
  have hi1 : r ^ i < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hp1 : r ^ i * r < 1 := by nlinarith
  have hp1pos : 0 < r ^ i * r := by positivity
  have hden : 0 < (1 - r ^ i) * (1 - (r ^ i * r) ^ 2) := by
    have hd1 : 0 < 1 - r ^ i := by linarith
    have hd2 : 0 < 1 - (r ^ i * r) ^ 2 := by nlinarith
    positivity
  exact div_pos (mul_pos hp (rootE_pos r hr hr1 i hi)) hden
