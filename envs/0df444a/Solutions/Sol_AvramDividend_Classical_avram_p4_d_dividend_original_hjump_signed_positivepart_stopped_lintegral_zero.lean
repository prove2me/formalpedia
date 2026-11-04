-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:11:31.226751+00:00
-- url     : https://prove2.me/submissions/43f58a83-da71-4de7-beed-55ea9d801443

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual size-dependent, source-ordered right-dividend signed residual has zero
    positive-part lintegral on the exact ruin-stopped Stieltjes reward set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)) *
        ((rightLimit D s.toNNReal ω - D s.toNNReal ω) +
          w (riskProcess X x D s.toNNReal ω -
            (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
          w (riskProcess X x D s.toNNReal ω)))
        ∂(dividendMeasure D ω)) = 0 := by
  have hPoint : ∀ s : ℝ, s ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T →
      Real.exp (-(q * s)) *
        ((rightLimit D s.toNNReal ω - D s.toNNReal ω) +
          w (riskProcess X x D s.toNNReal ω -
            (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
          w (riskProcess X x D s.toNNReal ω)) ≤ 0 := by
    intro s hs
    have hsPay := hs.1
    change s ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {t : ℝ | ENNReal.ofReal t < ruinTime X x D ω}) at hsPay
    have hPreS : s.toNNReal = 0 ∨
        (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
      rcases hsPay.2 with hzero | hlt
      · left
        have heq : s = 0 := by simpa using hzero
        simp only [heq, Real.toNNReal_zero]
      · right
        change (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hlt
        exact hlt
    have hSec := hjump ω s.toNNReal hPreS
    have hSigned : (rightLimit D s.toNNReal ω - D s.toNNReal ω) +
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
        w (riskProcess X x D s.toNNReal ω) ≤ 0 := by
      linarith only [hSec]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hSigned
  calc
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)) *
        ((rightLimit D s.toNNReal ω - D s.toNNReal ω) +
          w (riskProcess X x D s.toNNReal ω -
            (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
          w (riskProcess X x D s.toNNReal ω)))
        ∂(dividendMeasure D ω))
      = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          (0 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
            apply MeasureTheory.lintegral_congr_ae
            filter_upwards [MeasureTheory.ae_restrict_mem
              (MeasurableSet.inter (paymentTimes_measurable _) measurableSet_Iic)] with s hs
            exact ENNReal.ofReal_eq_zero.mpr (hPoint s hs)
    _ = 0 := by simp