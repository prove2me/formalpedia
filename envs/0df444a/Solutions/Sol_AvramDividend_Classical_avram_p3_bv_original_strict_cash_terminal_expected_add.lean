-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_terminal_expected_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:53:20.785177+00:00
-- url     : https://prove2.me/submissions/c18fe705-35ee-433f-a39b-b1b2da9c4a2f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original pre-rightpayment stochastic budget splits into its
    separately integrable strict dividend cash and signed preterminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let CashOpen : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0
    (∫ ω, CashOpen ω + Pre ω ∂P) =
      (∫ ω, CashOpen ω ∂P) + (∫ ω, Pre ω ∂P) := by
  dsimp only
  letI : IsProbabilityMeasure P := X.isProbability
  have hCash := avram_p3_bv_original_strict_cash_L1
    X x C D hD q hq T hT
  have hPre := avram_p3_bv_original_strict_preterminal_L1
    X hBV X.X_zero inferInstance x D hD.1.1 w hw_cont hw_neg q
    (⟨T, hT⟩ : ℝ≥0)
  exact integral_add hCash hPre
