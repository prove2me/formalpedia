-- Prove2me | solution 1 for FamousTheorems.probability_measure_determined_by_cdf_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:47:54.87499+00:00
-- url     : https://prove2.me/submissions/60d67614-7308-435f-938a-c1f0d8387139

import Mathlib

theorem solution (μ ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (h : ProbabilityTheory.cdf μ = ProbabilityTheory.cdf ν) : μ = ν :=
  MeasureTheory.Measure.eq_of_cdf μ ν h
