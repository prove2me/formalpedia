-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_true_stopped_strictpre_deriv_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:28:23.800046+00:00
-- url     : https://prove2.me/submissions/31c35338-45a7-4447-b76b-f73ed422d9e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A compact strictly interior reserve band makes the genuine stopped
left-source/right-dividend-limit gradient integrable against the original
dividend Stieltjes measure, including its singular and atomic parts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable
      (fun s : ℝ => deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω))
      ((dividendMeasure D ω).restrict
        (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂(dividendMeasure D ω).restrict
        (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => deriv w (x +
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
      rightLimit D s.toNNReal ω))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by
  obtain ⟨K, _, hK⟩ :=
    avram_p4_d_dividend_ubv_compact_interior_derivative_bound
      C w hwC2 a b hab hBand
  apply avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
    D hD ω σ T _ hSM K
  filter_upwards [hstate] with s hs
  simpa only [Real.norm_eq_abs] using hK _ hs
