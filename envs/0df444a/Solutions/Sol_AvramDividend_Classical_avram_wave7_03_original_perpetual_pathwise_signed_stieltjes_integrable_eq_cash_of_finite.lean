-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:21:56.873137+00:00
-- url     : https://prove2.me/submissions/b2f48669-2a9e-4816-ad22-85997d134bad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under actual finite perpetual pathwise ENNReal dividends, the
    unrestricted original signed Stieltjes integral genuinely exists as
    an integrable real function and equals the full ENNReal cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ)
    (hCashFinite :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω))
      (dividendMeasure D ω) ∧
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by
  let S : Set ℝ := paymentTimes (ruinTime X x D ω)
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ := fun t => Real.exp (-(q * t))
  have hf : Measurable f := by
    dsimp [f]
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_id).neg)
  have hNonneg : 0 ≤ᵐ[μ.restrict S] f :=
    Filter.Eventually.of_forall
      (fun t => (Real.exp_pos (-(q * t))).le)
  have hInt : Integrable f (μ.restrict S) := by
    apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hf.aestronglyMeasurable hNonneg).mp
    exact ne_of_lt hCashFinite
  constructor
  · exact hInt
  · exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonneg
