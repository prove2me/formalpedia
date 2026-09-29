-- Prove2me | solution 1 for ErlerGross.mode_sum_eq_B3_identity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:18:49.777295+00:00
-- url     : https://prove2.me/submissions/43ddf2b0-3cb3-48b5-9005-fa443ba44a1b

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_mode_sum_eq_kappa_integral
import Theorems.Thm_ErlerGross_kappa_integral_eq_residue_sum

open Real Filter Topology MeasureTheory ErlerGross

theorem solution :
    HasSum (fun n : Nat => 3 * ErlerGross.neumannMEven (n + 1) *
      ErlerGross.betaVec (2 * (n + 1)))
      (2 * tsum (fun n : Nat => ErlerGross.b3Term (n + 1))) := by
  obtain ⟨_, hmode⟩ := ErlerGross.mode_sum_eq_kappa_integral
  have hb3 := ErlerGross.kappa_integral_eq_residue_sum
  rw [← hb3.tsum_eq] at hmode
  exact hmode