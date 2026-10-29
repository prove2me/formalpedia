-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_esscher_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:15:52.743912+00:00
-- url     : https://prove2.me/submissions/ffa814a3-1fea-496f-b541-adcd17a54747

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_joint_exp_clock_rate_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Inverse Esscher weighting at a real exponential clock is a clock-rate shift. -/
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
  let density : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (α * F z - q * z.2))
  let inverse : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-α * F z))
  have hd : Measurable density := by
    dsimp [density]
    fun_prop
  have hi : Measurable inverse := by
    dsimp [inverse]
    fun_prop
  have hIW : Measurable (fun z => inverse z * W z) := hi.mul hW
  have hProduct (z : Ω × ℝ) :
      density z * (inverse z * W z) =
        ENNReal.ofReal (Real.exp (-(q * z.2))) * W z := by
    rw [← mul_assoc]
    congr 1
    dsimp [density, inverse]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ, density z * (inverse z * W z)
        ∂(P.prod (expMeasure p))) := by
      rw [lintegral_withDensity_eq_lintegral_mul
        (P.prod (expMeasure p)) hd hIW]
      rfl
    _ = ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-(q * z.2))) * W z
          ∂(P.prod (expMeasure p))) := by
      congr 1
      apply lintegral_congr
      intro z
      exact hProduct z
    _ = _ :=
      avram_ws01e_bi_new_joint_exp_clock_rate_shift P p q hp hq W hW
