-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_stopped_diffuse_dividend_signed_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:58:40.985273+00:00
-- url     : https://prove2.me/submissions/97ee3232-e13b-42bf-973a-8e575e8bd96c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (V : ℝ → ℝ) (hSlope : ∀ y : ℝ, 1 ≤ deriv V y)
    (ω : Ω) (ρ : ℝ≥0)
    (hI : IntegrableOn (fun s : ℝ =>
      Real.exp (-(q * s)) *
        (1 - deriv V (riskProcess X x D (Real.toNNReal s) ω)))
      (Iio (ρ : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Iio (ρ : ℝ),
      Real.exp (-(q * s)) *
        (1 - deriv V (riskProcess X x D (Real.toNNReal s) ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall (fun s => by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact (Real.exp_pos _).le
    · exact sub_nonpos.mpr (hSlope _))
