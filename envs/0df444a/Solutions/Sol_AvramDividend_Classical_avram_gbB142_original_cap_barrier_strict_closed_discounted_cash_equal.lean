-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB142_original_cap_barrier_strict_closed_discounted_cash_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:04:53.004111+00:00
-- url     : https://prove2.me/submissions/8e27dac2-aa7d-4ce0-a5ff-0ce8a6961b9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original cap barrier closed and strict discounted Stieltjes cash coincide. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hAdm : IsAdmissibleLe X (1 / 8 : ℝ)
      (ENNReal.ofReal (1 / 8 : ℝ))
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) :
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ)
          (1 / 8 : ℝ)) ω)).toReal =
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ)
          (1 / 8 : ℝ)) ω)).toReal := by
  have h :=
    avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
      X (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) hAdm
      ω q hq S
  have hNoAtom :=
    avram_gbB41_original_barrier_postpayment_rightLimit_eq
      X (1 / 8 : ℝ) ω S
  rw [hNoAtom] at h
  simpa only [sub_self, mul_zero, ite_self, add_zero] using h
