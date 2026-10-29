-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_exp_supremum_strict_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:11:09.77974+00:00
-- url     : https://prove2.me/submissions/146c9a1d-d622-437b-8475-48e2aa3d617e

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_Reflection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A genuine exponential pushforward law gives a strictly positive observable
almost surely, including the absence of an atom at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hS : Measurable S)
    (hLaw : Measure.map S μ = expMeasure lam) :
    ∀ᵐ z ∂μ, 0 < S z := by
  haveI : IsProbabilityMeasure (expMeasure lam) :=
    isProbabilityMeasure_expMeasure hlam
  have hCDF0 : (cdf (expMeasure lam)) 0 = 0 := by
    simpa using (cdf_expMeasure_eq hlam 0)
  have hMass0 : expMeasure lam (Iic (0 : ℝ)) = 0 := by
    calc
      expMeasure lam (Iic (0 : ℝ)) =
          ENNReal.ofReal ((cdf (expMeasure lam)) 0) :=
            (ofReal_cdf (expMeasure lam) 0).symm
      _ = 0 := by simp only [hCDF0, ENNReal.ofReal_zero]
  have hBad : μ {z : Ω | S z ≤ 0} = 0 := by
    have hMap := congrArg
      (fun (ν : Measure ℝ) => ν (Iic (0 : ℝ))) hLaw
    rw [Measure.map_apply hS measurableSet_Iic] at hMap
    exact hMap.trans hMass0
  rw [ae_iff]
  simpa only [not_lt] using hBad
