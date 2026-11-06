-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_strict_discounted_cash_real_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:37:13.493107+00:00
-- url     : https://prove2.me/submissions/29120215-e929-4a13-a458-a14137ef477d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original strict discounted cash grows monotonically with the real horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * r)))
        ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩ Iio t,
      ENNReal.ofReal (Real.exp (-(q * r)))
        ∂(dividendMeasure D ω)).toReal := by
  have ht : 0 ≤ t := hs.trans hst
  have hfinite :=
    avram_limit2_original_strict_discounted_cash_finite_all_paths
      X q hq x D hD ω t ht
  have hsub :
      paymentTimes (ruinTime X x D ω) ∩ Iio s ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iio t := by
    intro r hr
    exact ⟨hr.1, lt_of_lt_of_le hr.2 hst⟩
  exact ENNReal.toReal_mono hfinite (lintegral_mono_set hsub)
