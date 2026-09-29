-- Prove2me | solution 2 for ErlerGross.B3_series_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:12:13.193128+00:00
-- url     : https://prove2.me/submissions/7f7bb88b-abb7-4c49-952f-7db4ba67766a

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_B3_series_double_integral
import Theorems.Thm_ErlerGross_B3_double_integral_eval

open Real Filter Topology MeasureTheory ErlerGross

theorem solution :
    HasSum (fun n : Nat => ErlerGross.b3Term (n + 1)) (-Real.log (27 / 16) / 2) := by
  have h := ErlerGross.B3_series_double_integral
  rw [ErlerGross.B3_double_integral_eval] at h
  convert h using 1 <;> ring