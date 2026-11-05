-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_all_horizon_closed_postreward_le_strict_or_zero_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:48:35.524194+00:00
-- url     : https://prove2.me/submissions/b6fe65bf-00f4-4150-a4a1-99268b92431c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A uniform, sharp original-process stopped-reward bridge across all horizons.
At zero the separately paid initial right atom requires the initial value w(x);
at every positive horizon the strict prepayment reserve covers the sole
right-horizon dividend and surviving postpayment reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) *
        w (x + X.X S ω - rightLimit D S ω)
     else 0) ≤
    (if S = 0 then w x
     else
       (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
        else 0)) := by
  by_cases hs : S = 0
  · subst S
    simpa using
      (avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
        X hBV q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD hjump ω)
  · have hpos : (0 : ℝ≥0) < S :=
      lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ S) (Ne.symm hs)
    have hbudget :=
      avram_p3_c_bvchain_original_canonical_signed_horizon_correction
        X x C D hD w hjump ω S hpos q hq
    simpa [hs] using hbudget
