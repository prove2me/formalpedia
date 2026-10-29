-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_cast_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:24:09.221451+00:00
-- url     : https://prove2.me/submissions/8cd836df-55ca-4012-8e0d-227fd1bbad4a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_esscher_weight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Inverse terminal Esscher weighting uses the genuine toNNReal observation age. -/
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
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hTail : expMeasure p (Ioi (0 : ℝ)) = 1 := by
    simpa using
      (avram_ws01e_b_expMeasure_strict_survival_real p 0 hp le_rfl)
  have hCompl : expMeasure p (Iic (0 : ℝ)) = 0 := by
    have hc := measure_compl (μ := expMeasure p)
      measurableSet_Ioi (measure_ne_top (expMeasure p) (Ioi (0 : ℝ)))
    simpa [hTail] using hc
  have hClockPos : ∀ᵐ t : ℝ ∂expMeasure p, 0 < t := by
    apply ae_iff.mpr
    simpa only [not_lt, Set.Iic] using hCompl
  have hClock : ∀ᵐ t : ℝ ∂expMeasure p, 0 ≤ t :=
    hClockPos.mono (fun _ ht => ht.le)
  have hProd : ∀ᵐ z : Ω × ℝ ∂(P.prod (expMeasure p)), 0 ≤ z.2 := by
    have hSet : MeasurableSet {z : Ω × ℝ | 0 ≤ z.2} :=
      measurableSet_le measurable_const measurable_snd
    rw [Measure.ae_prod_iff_ae_ae hSet]
    exact Filter.Eventually.of_forall (fun _ => hClock)
  have hEqual : (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (α * F z - (Real.toNNReal z.2 : ℝ) * q))) =
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (α * F z - q * z.2))) := by
    apply withDensity_congr_ae
    filter_upwards [hProd] with z hz
    have ht : (Real.toNNReal z.2 : ℝ) = z.2 :=
      Real.coe_toNNReal z.2 hz
    simp only [ht]
    congr 2
    ring
  rw [hEqual]
  exact avram_ws01e_bi_new_inverse_clock_esscher_weight
    P p q α hp hq F hF W hW
