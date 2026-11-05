-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_independent_disjoint_mark_band_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:24:37.126797+00:00
-- url     : https://prove2.me/submissions/4994c37e-6880-49a8-b5d5-ebdce8fd6167

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

/-- Independent finite-band original marked-jump counts have orthogonal
physical compensated increments when both source first moments hold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (A B : Set ℝ) (hDisjoint : Disjoint A B)
    (JA JB : Ω → ℝ)
    (hSourceA : ∀ ω, JA ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ A)).toReal)
    (hSourceB : ∀ ω, JB ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJA : Integrable JA P) (hJB : Integrable JB P)
    (hCrossInt : Integrable (fun ω => JA ω * JB ω) P)
    (hMeasA : AEStronglyMeasurable JA P)
    (hMeasB : AEStronglyMeasurable JB P)
    (hIndependent : IndepFun JA JB P)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirstA : (∫ ω, JA ω ∂P) = rA)
    (hFirstB : (∫ ω, JB ω ∂P) = rB) :
    (∫ ω, (JA ω - rA) * (JB ω - rB) ∂P) = 0 := by
  have hCross : (∫ ω, JA ω * JB ω ∂P) = rA * rB := by
    rw [IndepFun.integral_fun_mul_eq_mul_integral
      hIndependent hMeasA hMeasB, hFirstA, hFirstB]
  exact avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality
    X s t A B hDisjoint JA JB hSourceA hSourceB
    hJA hJB hCrossInt rA rB hRateA hRateB hFirstA hFirstB hCross
