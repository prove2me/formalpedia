-- Prove2me | solution 1 for AvramDividend.Classical.drained_zero_barrier_expected_reward_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:53:50.626476+00:00
-- url     : https://prove2.me/submissions/4d806cdb-3629-430b-b84a-2ed23648a3fa

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_finite_horizon_reward_lower_bound
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The pathwise initial-capital reward survives integration over the
    probability space of the Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (q T : ℝ) (hT : 0 ≤ T) :
    ENNReal.ofReal x ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes
          (ruinTime X x
            (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hmono :
      (∫⁻ _ : Ω, ENNReal.ofReal x ∂P) ≤
        (∫⁻ ω, ∫⁻ t in paymentTimes
            (ruinTime X x
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure
                (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∂P) := by
    apply lintegral_mono
    intro ω
    exact drained_zero_barrier_finite_horizon_reward_lower_bound
      X x hx q T hT ω
  have hconst :
      (∫⁻ _ : Ω, ENNReal.ofReal x ∂P) = ENNReal.ofReal x := by
    simp
  exact hconst ▸ hmono
