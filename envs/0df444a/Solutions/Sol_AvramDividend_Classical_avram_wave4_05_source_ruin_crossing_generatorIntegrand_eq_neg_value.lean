-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_ruin_crossing_generatorIntegrand_eq_neg_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:58:35.693985+00:00
-- url     : https://prove2.me/submissions/07d08dd6-4eb7-48da-9351-11cdf5062360

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At reserves at least one unit above the cap, every large jump crossing
strictly below ruin contributes precisely minus the pre-jump candidate value. -/
theorem solution
    (W : ℝ → ℝ) (x y : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x)
    (hruin : y < -x) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y =
      -vcstar W x := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx1 : 1 ≤ x := by dsimp [a] at *; linarith
  have hyneg : y < 0 := by linarith
  have hlarge : y ≤ -1 := by linarith
  have hxyneg : x + y < 0 := by linarith
  have hz : vcstar W (x + y) = 0 := by
    change barrierValue W a (x + y) = 0
    simp [barrierValue, hxyneg]
  rw [avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
    W x y hfar hyneg, if_pos hlarge, hz]
  simp
