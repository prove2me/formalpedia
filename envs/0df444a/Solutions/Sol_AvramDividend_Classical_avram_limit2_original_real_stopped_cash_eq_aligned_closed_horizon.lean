-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_real_stopped_cash_eq_aligned_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:14:54.413902+00:00
-- url     : https://prove2.me/submissions/488d5dab-936c-4edb-b75e-2d5b4651b1e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_real_stopped_paymentTimes_subset_closed_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Set.Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  have hWindow (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Set.Iic T =
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) := by
    exact Set.inter_eq_left.mpr
      (avram_limit2_real_stopped_paymentTimes_subset_closed_horizon (ruinTime X x D ω) T hT)
  have hCash (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [hWindow ω]
  simp_rw [hCash]
