-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_immediate_ruin_closed_cash_le_candidate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:31:36.80355+00:00
-- url     : https://prove2.me/submissions/78662a69-0468-4a8b-9d0b-26a5f331e383

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Immediate original ruin leaves the physical closed-horizon initial atom only. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q T : ℝ) (hT : 0 < T)
    (hruin : ruinTime X x D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ w x := by
  have hstrict := avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
    X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD hjump ω q T hT hruin
  have hPay : paymentTimes (ruinTime X x D ω) = ({0} : Set ℝ) := by
    rw [hruin]
    simpa using (paymentTimes_min_zero_eq_singleton_zero (0 : ℝ≥0∞))
  have hWindow : paymentTimes (ruinTime X x D ω) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iio T := by
    rw [hPay]
    ext t
    simp only [mem_inter_iff, mem_singleton_iff, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨rfl, _⟩
      exact ⟨rfl, hT⟩
    · rintro ⟨rfl, _⟩
      exact ⟨rfl, le_of_lt hT⟩
  rw [hWindow]
  exact hstrict
