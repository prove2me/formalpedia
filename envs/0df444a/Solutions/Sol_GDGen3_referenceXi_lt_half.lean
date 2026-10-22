-- Prove2me | solution 1 for GDGen3.referenceXi_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:23:11.581775+00:00
-- url     : https://prove2.me/submissions/6e2625e3-3895-4689-84a8-cf37949aa69d

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    referenceXi r i < (i : ℝ) / 2 := by
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hri : 1 < 1 / r ^ i := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ i)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i ≠ 0)
  have hri1 : 1 < 1 / r ^ (i + 1) := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ (i + 1))).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
  unfold referenceXi
  apply (div_lt_iff₀ (by positivity : 0 < (1 + r) * (1 + 1 / r ^ (i + 1)))).2
  have hm := mul_pos hip (show 0 < (1 + r) * (1 / r ^ (i + 1) - 1) by positivity)
  nlinarith
