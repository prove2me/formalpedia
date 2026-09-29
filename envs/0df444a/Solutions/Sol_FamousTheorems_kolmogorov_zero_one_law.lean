-- Prove2me | solution 1 for FamousTheorems.kolmogorov_zero_one_law
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:31:06.198414+00:00
-- url     : https://prove2.me/submissions/41527ff5-a5fe-47dd-b985-f0119f5a7b03

import Mathlib

open scoped MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} (s : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, s n ≤ m0) (h_indep : ProbabilityTheory.iIndep s μ) {t : Set Ω}
    (ht_tail : MeasurableSet[Filter.limsup s Filter.atTop] t) : μ t = 0 ∨ μ t = 1 :=
  ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail
