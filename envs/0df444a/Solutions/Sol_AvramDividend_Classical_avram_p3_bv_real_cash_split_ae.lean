-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_real_cash_split_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:02:33.003786+00:00
-- url     : https://prove2.me/submissions/3a88799f-6ec5-440e-8b4f-9b556b7e8be8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_real_cash_split
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under an actual original admissible dividend strategy, the finite
    closed-horizon real-valued cash split holds almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  let S : ℝ≥0 := ⟨T, hT⟩
  have hfinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ :=
    avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
      X x C D hD q (fun _ => S) S (fun _ => le_rfl)
  filter_upwards [hfinite] with ω hω
  have hSval : (S : ℝ) = T := rfl
  exact avram_p3_bv_closed_horizon_real_cash_split
    X x D q T ω (paymentTimes_measurable (ruinTime X x D ω))
    (by simpa only [hSval] using hω)
