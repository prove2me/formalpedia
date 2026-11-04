-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_weighted_log_test_continuousOn_negative_exp_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:57:50.432885+00:00
-- url     : https://prove2.me/submissions/4dc2428d-129e-43c7-9a9a-b3d60bcffaf1

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On the strict negative-jump exponential coordinate band (0,1),
the inverse-weighted logarithmic test transform is continuous. -/
theorem solution
    (f : ℝ → ℝ) (hf : Continuous f) :
    ContinuousOn
      (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4)
      (Ioo (0 : ℝ) 1) := by
  intro z hz
  have hz1 : z - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_lt hz.2)
  have hnum : ContinuousAt (fun v : ℝ => f (Real.log v)) z :=
    hf.continuousAt.comp (Real.continuousAt_log (ne_of_gt hz.1))
  have hden : ContinuousAt (fun v : ℝ => (v - 1) ^ 4) z := by
    fun_prop
  exact (hnum.div hden (pow_ne_zero 4 hz1)).continuousWithinAt
