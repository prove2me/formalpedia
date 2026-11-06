-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_strict_discounted_cash_finite_all_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:47:30.138988+00:00
-- url     : https://prove2.me/submissions/d9510bf3-3e54-4260-9d69-945c2e817f8f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Actual original strict Iio stopped discounted cash has finite mass at every nonnegative finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≠ ⊤ := by
  change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iio (((⟨T, hT⟩ : ℝ≥0) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≠ ⊤
  have hsubset :
      paymentTimes (ruinTime X x D ω) ∩ Iio (((⟨T, hT⟩ : ℝ≥0) : ℝ)) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (((⟨T, hT⟩ : ℝ≥0) : ℝ)) := by
    intro t ht
    exact ⟨ht.1, Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp ht.2))⟩
  have hstrict :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((⟨T, hT⟩ : ℝ≥0) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((⟨T, hT⟩ : ℝ≥0) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) :=
    lintegral_mono_set hsubset
  exact ne_of_lt (lt_of_le_of_lt
    (hstrict.trans
      (avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
        q hq D hD ω (ruinTime X x D ω) ⟨T, hT⟩))
    ENNReal.ofReal_lt_top)
