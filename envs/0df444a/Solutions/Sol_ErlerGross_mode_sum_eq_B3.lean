-- Prove2me | solution 1 for ErlerGross.mode_sum_eq_B3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:04:24.428969+00:00
-- url     : https://prove2.me/submissions/da9a51fe-b610-4751-92e6-32fe7d53406f

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_mode_sum_eq_B3_summable
import Theorems.Thm_ErlerGross_mode_sum_eq_B3_identity

open Real Filter Topology MeasureTheory

theorem solution :
    Summable (fun n : ℕ => ErlerGross.b3Term (n + 1)) ∧
      HasSum (fun n : ℕ => 3 * ErlerGross.neumannMEven (n + 1) *
        ErlerGross.betaVec (2 * (n + 1)))
        (2 * ∑' n : ℕ, ErlerGross.b3Term (n + 1)) := by
  exact ⟨ErlerGross.mode_sum_eq_B3_summable,
    ErlerGross.mode_sum_eq_B3_identity⟩
