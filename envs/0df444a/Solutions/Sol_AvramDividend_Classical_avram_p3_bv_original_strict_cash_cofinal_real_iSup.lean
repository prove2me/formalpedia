-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_real_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:59:19.845346+00:00
-- url     : https://prove2.me/submissions/71fc8fc1-4e80-4238-81ce-7844afb80dbd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finiteness of the genuine full Stieltjes cash allows the original
cofinal ENNReal limit to pass exactly to the real discounted budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n)
    (hfinite : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤) :
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by
  have hbelow' (n : ℕ) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
    lt_of_le_of_lt
      (avram_p3_bv_original_cash_strict_horizon_mono X x q
        (u n) T (hbelow n) D ω) hfinite
  calc
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
      (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω)).toReal := by
          symm
          exact ENNReal.toReal_iSup (fun n => ne_of_lt (hbelow' n))
    _ = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by
          rw [avram_p3_bv_original_strict_cash_cofinal_unconditional
            X x q T D ω u hmono hbelow hcover]
