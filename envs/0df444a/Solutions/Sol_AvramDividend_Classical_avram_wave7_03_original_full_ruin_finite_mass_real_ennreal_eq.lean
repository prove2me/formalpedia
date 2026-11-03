-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:33:24.935842+00:00
-- url     : https://prove2.me/submissions/8d648025-fdb9-4097-baf2-082ef2046a79

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original ruin-stopped signed-to-ENNReal dividend bridge on the
    complete real-time payment domain, assuming finite Stieltjes mass there. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    (q : ℝ) (hq : 0 ≤ q)
    (hMass : (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ≠ ⊤) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  have hA : MeasurableSet
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) :=
    (paymentTimes_measurable _).inter measurableSet_Iic
  have hAnonneg : ∀ t ∈
      paymentTimes (ruinTime X x D ω) ∩ Iic T, 0 ≤ t := by
    intro t ht
    exact ht.1.1
  exact discounted_stieltjes_finite_measure_payout_bridge
    q hq (dividendMeasure D ω)
    (paymentTimes (ruinTime X x D ω) ∩ Iic T)
    hA hAnonneg hMass
