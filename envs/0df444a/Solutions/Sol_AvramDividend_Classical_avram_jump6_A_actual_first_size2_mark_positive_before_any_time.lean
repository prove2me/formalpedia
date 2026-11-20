-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_first_size2_mark_positive_before_any_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:35:09.467483+00:00
-- url     : https://prove2.me/submissions/64831b6a-58ed-4dda-8b73-6deb5fb3cb85

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_rateone_exponential_first_arrival_cdf_positive_of_pos
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
      (Measure.dirac (-2 : ℝ)) μ)
    (t : ℝ) (ht : 0 < t) :
    0 < μ {ω : Ω | τ 0 ω ≤ t} := by
  letI : IsProbabilityMeasure μ := hJ.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hCDF : 0 < cdf (expMeasure (1 : ℝ)) t :=
    avram_jump6_A_rateone_exponential_first_arrival_cdf_positive_of_pos t ht
  have hReal : 0 < ((expMeasure (1 : ℝ)) (Iic t)).toReal := by
    simpa only [cdf_eq_real, Measure.real_def] using hCDF
  have hMass : 0 < (expMeasure (1 : ℝ)) (Iic t) :=
    (ENNReal.toReal_pos_iff.mp hReal).1
  have heq : μ {ω : Ω | τ 0 ω ≤ t} = (expMeasure (1 : ℝ)) (Iic t) := by
    change μ ((τ 0) ⁻¹' Iic t) = _
    rw [← Measure.map_apply (hJ.measurable_interarrival 0) measurableSet_Iic]
    exact congrArg (fun ν : Measure ℝ => ν (Iic t))
      (hJ.law_interarrival 0).map_eq
  rw [heq]
  exact hMass
