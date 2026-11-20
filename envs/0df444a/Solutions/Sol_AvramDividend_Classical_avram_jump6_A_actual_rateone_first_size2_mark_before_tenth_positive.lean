-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_rateone_first_size2_mark_before_tenth_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:33:05.50058+00:00
-- url     : https://prove2.me/submissions/fa004ae1-0b89-4867-ac4b-d0d599502a42

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_rateone_early_negative_mark_arrival_positive_cdf
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    0 < μ {ω : Ω | τ 0 ω ≤ (1 / 10 : ℝ)} := by
  letI : IsProbabilityMeasure μ := hJ.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hCDF :
      0 < cdf (expMeasure (1 : ℝ)) (1 / 10 : ℝ) :=
    AvramDividend.Classical.avram_jump6_A_rateone_early_negative_mark_arrival_positive_cdf
  have hReal : 0 < ((expMeasure (1 : ℝ)) (Iic (1 / 10 : ℝ))).toReal := by
    simpa only [cdf_eq_real, Measure.real_def] using hCDF
  have hMass : 0 < (expMeasure (1 : ℝ)) (Iic (1 / 10 : ℝ)) :=
    (ENNReal.toReal_pos_iff.mp hReal).1
  have heq :
      μ {ω : Ω | τ 0 ω ≤ (1 / 10 : ℝ)} =
        (expMeasure (1 : ℝ)) (Iic (1 / 10 : ℝ)) := by
    change μ ((τ 0) ⁻¹' Iic (1 / 10 : ℝ)) = _
    rw [← Measure.map_apply (hJ.measurable_interarrival 0) measurableSet_Iic]
    exact congrArg (fun ν : Measure ℝ => ν (Iic (1 / 10 : ℝ)))
      (hJ.law_interarrival 0).map_eq
  rw [heq]
  exact hMass
