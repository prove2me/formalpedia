-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_increment_tail_stationary_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:32:09.308425+00:00
-- url     : https://prove2.me/submissions/624f902a-d471-4a98-a75b-dda2c1f8f2e2

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (M : ℝ) :
    (∫ ω,
      if M < (X.drift * (t : ℝ) - X.X t ω) -
             (X.drift * (s : ℝ) - X.X s ω)
      then (X.drift * (t : ℝ) - X.X t ω) -
             (X.drift * (s : ℝ) - X.X s ω) else 0 ∂P)
    = (∫ ω,
      if M < X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t-s) ω
      then X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t-s) ω
      else 0 ∂P) := by
  have hf : Measurable (fun z : ℝ => if M < z then z else 0) := by
    have hs : MeasurableSet {z : ℝ | M < z} := measurableSet_Ioi
    exact Measurable.ite hs measurable_id measurable_const
  have hi := (actual_levy_drift_deficit_stationary_increment_law X s t hst).comp hf
  simpa only [Function.comp_def] using hi.integral_eq