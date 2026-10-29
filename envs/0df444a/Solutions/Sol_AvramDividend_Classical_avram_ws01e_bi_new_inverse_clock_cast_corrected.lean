-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_cast_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:23:29.797375+00:00
-- url     : https://prove2.me/submissions/dac0356a-8e32-4365-899b-bf61ac0caa61

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_esscher_weight

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
            ENNReal.ofReal (Real.exp
              (α * F z - (Real.toNNReal z.2 : ℝ) * q))))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, W z ∂(P.prod (expMeasure (p + q)))) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  have hsurv := AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real p 0 hp le_rfl
  have hneg : ProbabilityTheory.expMeasure p (Set.Iic 0) = 0 := by
    have h1 : ProbabilityTheory.expMeasure p (Set.Ioi 0) = 1 := by simpa using hsurv
    rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, h1, tsub_self]
  have hae : ∀ᵐ z ∂(P.prod (ProbabilityTheory.expMeasure p)), 0 ≤ z.2 := by
    rw [ae_iff]
    have : {z : Ω × ℝ | ¬ 0 ≤ z.2} ⊆ Set.univ ×ˢ Set.Iic 0 := by
      intro z hz; simp only [Set.mem_setOf_eq, not_le] at hz
      exact ⟨trivial, le_of_lt hz⟩
    refine measure_mono_null this ?_
    rw [Measure.prod_prod, hneg, mul_zero]
  have hEq : (P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (α * F z - (Real.toNNReal z.2 : ℝ) * q))) =
      (P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (α * F z - q * z.2))) := by
    apply withDensity_congr_ae
    filter_upwards [hae] with z hz
    rw [Real.coe_toNNReal _ hz]
    congr 2
    ring
  rw [hEq]
  exact AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_esscher_weight P p q α hp hq F hF W hW
