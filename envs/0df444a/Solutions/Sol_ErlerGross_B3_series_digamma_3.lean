-- Prove2me | solution 3 for ErlerGross.B3_series_digamma
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:43:07.335548+00:00
-- url     : https://prove2.me/submissions/631d0c4c-15ea-4ed4-8bde-87c3683c218a

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_B3_series_closed_form
import Theorems.Thm_ErlerGross_B3_digamma_values

open Real Filter Topology MeasureTheory

theorem solution :
    HasSum (fun n : ℕ => ((ErlerGross.b3Term (n + 1) : ℝ) : ℂ))
      (Complex.digamma ((2 : ℂ) / 3) / 2 + Complex.digamma ((1 : ℂ) / 3) / 2 -
        Complex.digamma ((1 : ℂ) / 2)) := by
  have h := ErlerGross.B3_series_closed_form
  have hC : HasSum (fun n : ℕ => ((ErlerGross.b3Term (n + 1) : ℝ) : ℂ))
      (((-Real.log (27 / 16) / 2 : ℝ) : ℂ)) := by
    simpa using Complex.ofRealCLM.hasSum h
  rw [ErlerGross.B3_digamma_values]
  exact hC
