-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:39:56.96452+00:00
-- url     : https://prove2.me/submissions/e6696bdb-0556-47aa-a0bb-6cdc7ed867f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2)
      y (-2 : ℝ) = -(1 + y + y ^ 2) := by
  have hNeg : y + (-2 : ℝ) < 0 := by linarith
  have hPos : ¬ y < 0 := not_lt_of_ge hy
  simp [SpectrallyNegativeLevy.generatorIntegrand, hNeg, hPos]
