-- Prove2me | solution 2 for GDGen3.pj_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:38:18.830411+00:00
-- url     : https://prove2.me/submissions/52212c98-faa6-43a0-9f31-94f1798fd643

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_geometric

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : StrictMono (pj r) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : 2 ≠ 0)
  intro a b hab
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  exact div_lt_div_of_pos_right (sub_lt_sub_right (pow_lt_pow_right₀ hz hab) 1) (by norm_num)
