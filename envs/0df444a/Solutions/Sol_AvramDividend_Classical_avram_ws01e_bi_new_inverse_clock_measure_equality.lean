-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_measure_equality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:35:29.424726+00:00
-- url     : https://prove2.me/submissions/d422574d-5048-4732-9581-58fdc7aaae3e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_cast_corrected

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q α : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (F : Ω × ℝ → ℝ) (hF : Measurable F) :
    ENNReal.ofReal (p + q) •
      (((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (α * F z - (Real.toNNReal z.2 : ℝ) * q)))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (-α * F z)))) =
    ENNReal.ofReal p • (P.prod (expMeasure (p + q))) := by
  ext S hS
  have h := AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_cast_corrected P p q α hp hq F hF
    (S.indicator 1) (measurable_one.indicator hS)
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, withDensity_apply _ hS,
    ← lintegral_indicator hS, ← lintegral_indicator_one hS]
  convert h using 3
  funext z
  by_cases hz : z ∈ S <;> simp [hz]
