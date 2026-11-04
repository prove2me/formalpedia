-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_exponential_jump_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:42:25.103878+00:00
-- url     : https://prove2.me/submissions/04ade9e2-bec0-49dd-8136-abab9abfc13b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual BV jump magnitudes dominate the physical-drift-normalised
source exponential at every finite horizon, before any compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᵐ ω ∂P,
      Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) ≤
        Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) := by
  filter_upwards
    [avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
      X hBV,
     avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
      X hBV] with ω hDrift hEncoding
  have hb := hDrift 0 T (by positivity)
  have he := hEncoding T
  simp only [NNReal.coe_zero, zero_sub, sub_zero] at hb
  rw [X.X_zero ω] at hb
  simp only [sub_zero] at hb
  have hXle : X.X T ω - (T : ℝ) * X.drift ≤ -(∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by
    linarith only [hb, he]
  have hm := mul_le_mul_of_nonneg_left hXle hθ
  exact Real.exp_le_exp.mpr (by nlinarith only [hm])
