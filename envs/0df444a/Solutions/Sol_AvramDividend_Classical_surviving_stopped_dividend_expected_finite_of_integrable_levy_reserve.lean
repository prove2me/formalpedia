-- Prove2me | solution 1 for AvramDividend.Classical.surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:44:02.45173+00:00
-- url     : https://prove2.me/submissions/7f9db1cf-9d90-4eae-9735-d59a5bb4d3cf

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_le_uncontrolled_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (hXI : Integrable (fun ω => x + X.X S ω) P) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≠ ⊤ := by
  have hPositive : Integrable (fun ω => max (x + X.X S ω) 0) P :=
    hXI.pos_part
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ max (x + X.X S ω) 0 :=
    Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have hFinite :
      (∫⁻ ω, ENNReal.ofReal (max (x + X.X S ω) 0) ∂P) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hPositive.aestronglyMeasurable hNonneg).2 hPositive
  have hBound :
      (∫⁻ ω, ENNReal.ofReal (x + X.X S ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (max (x + X.X S ω) 0) ∂P) := by
    apply lintegral_mono
    intro ω
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hExpected :=
    surviving_stopped_dividend_expected_le_uncontrolled_reserve
      X x D hD q hq σ T S hTS
  exact ne_of_lt (lt_of_le_of_lt (hExpected.trans hBound)
    (lt_top_iff_ne_top.mpr hFinite))
