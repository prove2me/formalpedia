-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_esscher_weight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:17:16.112096+00:00
-- url     : https://prove2.me/submissions/9a95dd26-7f9c-46b4-bed1-665dc57db856

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_joint_exp_clock_rate_shift

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q α : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (F : Ω × ℝ → ℝ) (hF : Measurable F)
    (W : Ω × ℝ → ℝ≥0∞) (hW : Measurable W) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-α * F z)) * W z
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ =>
            ENNReal.ofReal (Real.exp (α * F z - q * z.2))))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, W z ∂(P.prod (expMeasure (p + q)))) := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have h := AvramDividend.Classical.avram_ws01e_bi_new_joint_exp_clock_rate_shift P p q hp hq W hW
  rw [← h]
  congr 1
  apply lintegral_congr
  intro z
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3
  ring
