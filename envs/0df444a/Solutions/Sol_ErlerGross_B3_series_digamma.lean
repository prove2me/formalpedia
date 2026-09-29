-- Prove2me | solution 1 for ErlerGross.B3_series_digamma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:41:17.855989+00:00
-- url     : https://prove2.me/submissions/43f3f628-6fc3-4e65-89d7-f9c7b19aee94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
