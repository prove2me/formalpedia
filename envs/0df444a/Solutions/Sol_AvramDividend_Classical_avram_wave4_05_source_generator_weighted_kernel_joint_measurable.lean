-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_generator_weighted_kernel_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:50:39.292189+00:00
-- url     : https://prove2.me/submissions/a2e8855b-449b-4d9a-ac6d-b3ae11dd4aad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Joint Borel measurability of the *actual* source compensated
    jump kernel and its exponentially weighted absolute value. -/
theorem solution
    (W : ℝ → ℝ) (hW : Measurable W)
    (hdW : Measurable (deriv W)) (θ : ℝ) :
    Measurable
      (fun p : ℝ × ℝ => Real.exp (-θ * p.1) *
        |SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2|) := by
  have hind : Measurable
      (fun y : ℝ => (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hker : Measurable
      (fun p : ℝ × ℝ => SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    fun_prop
  fun_prop
