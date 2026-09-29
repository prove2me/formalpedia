-- Prove2me | solution 1 for FamousTheorems.chernoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:20:27.389829+00:00
-- url     : https://prove2.me/submissions/c6e35172-c9d7-464a-8f14-74e16f8b9363

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t : ℝ} [IsFiniteMeasure μ]
    (ε : ℝ) (ht : 0 ≤ t) (h_int : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t :=
  ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht h_int
