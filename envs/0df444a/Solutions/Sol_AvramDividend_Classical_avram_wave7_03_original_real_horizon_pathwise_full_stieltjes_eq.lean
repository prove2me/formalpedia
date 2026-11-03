-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:29:59.649165+00:00
-- url     : https://prove2.me/submissions/6de42d3b-31b0-4e0e-ac37-ec96ce2bb2be

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Pathwise full ruin-stopped Stieltjes signed/ENNReal equality on an
    actual nonnegative real horizon, including the zero right-limit atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  have h := avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
    X x D hD ω T.toNNReal q hq
  simpa only [Real.coe_toNNReal T hT] using h
