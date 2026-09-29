-- Prove2me | solution 1 for FamousTheorems.bienayme_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:43.247925+00:00
-- url     : https://prove2.me/submissions/31503f14-7c7a-475e-8d7f-f74772bd0783

import Mathlib

theorem solution {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MeasureTheory.MemLp (X i) 2 μ)
    (h : (s : Set ι).Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) :
    ProbabilityTheory.variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, ProbabilityTheory.variance (X i) μ :=
  ProbabilityTheory.IndepFun.variance_sum hs h
