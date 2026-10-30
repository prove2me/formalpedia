-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_drifted_brownian_stationary_positive_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:32:41.981886+00:00
-- url     : https://prove2.me/submissions/f0006871-692a-4225-8e7e-ff0bb21cf08d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_increment_gaussian
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_gaussian_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

/-- Drifted Brownian stationary increments, through exact Gaussian laws. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (s t : ℝ≥0) (hst : s < t) :
    IdentDistrib
      (fun ω => (W.W (t : ℝ) ω - W.W (s : ℝ) ω) -
        ((t : ℝ) - (s : ℝ)))
      (fun ω => W.W ((t - s : ℝ≥0) : ℝ) ω -
        ((t - s : ℝ≥0) : ℝ)) P P := by
  have hs : (0 : ℝ) ≤ (s : ℝ) := NNReal.coe_nonneg s
  have hst' : (s : ℝ) < (t : ℝ) := by exact_mod_cast hst
  have hsub : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) :=
    NNReal.coe_sub hst.le
  have hvar : (t - s : ℝ≥0) =
      ⟨(t : ℝ) - (s : ℝ), sub_nonneg.mpr (le_of_lt hst')⟩ := by
    apply Subtype.ext
    exact hsub
  have hinc := W.drift_minus_one_increment_gaussian hs hst'
  have hmarg := W.drift_minus_one_gaussian_law (t - s)
  rw [hvar] at hmarg
  rw [hvar]
  exact hinc.identDistrib hmarg
