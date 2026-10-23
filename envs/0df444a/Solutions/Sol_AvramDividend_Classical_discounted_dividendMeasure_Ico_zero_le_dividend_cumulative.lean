-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividendMeasure_Ico_zero_le_dividend_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:52:09.775372+00:00
-- url     : https://prove2.me/submissions/7c0f87b2-617f-4e90-80e9-74ddb4f4411a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) :
    (∫⁻ s in Ico (0 : ℝ) (t : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (D t ω)  := by
  calc
    (∫⁻ s in Ico (0 : ℝ) (t : ℝ),
       ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        (∫⁻ s in Ico (0 : ℝ) (t : ℝ),
          (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
      have hqs : 0 ≤ q * s := mul_nonneg hq hs.1
      have he : Real.exp (-(q * s)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr hqs
      simpa using (ENNReal.ofReal_le_ofReal he)
    _ = dividendMeasure D ω (Ico (0 : ℝ) (t : ℝ)) := by
      rw [lintegral_one, Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (D t ω) :=
      AvramDividend.Classical.dividendMeasure_Ico_zero_eq_dividendValue D hD ω t
