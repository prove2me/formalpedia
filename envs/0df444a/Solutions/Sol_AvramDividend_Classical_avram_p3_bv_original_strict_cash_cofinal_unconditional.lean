-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:44:07.755186+00:00
-- url     : https://prove2.me/submissions/6ebd24a7-a507-4de6-8a81-3412644db4ea

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual source payment-time measurability discharges the measurable
restriction hypothesis in the strict cofinal cash convergence theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
      ⨆ n, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by
  apply avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
    X x q T D ω u hmono hbelow hcover
  intro n
  exact (paymentTimes_measurable _).inter measurableSet_Iio
