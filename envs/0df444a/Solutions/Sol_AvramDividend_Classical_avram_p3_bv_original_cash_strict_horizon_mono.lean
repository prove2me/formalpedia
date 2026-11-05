-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_cash_strict_horizon_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:39:18.373957+00:00
-- url     : https://prove2.me/submissions/5a9894eb-6121-4e0c-b4fb-239eb8177cd0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original stopped discounted dividend measure accumulates monotonically
as a strict real horizon increases, including all diffuse and right-atomic mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q a b : ℝ) (hab : a ≤ b)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio a,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio b,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  exact ⟨ht.1, lt_of_lt_of_le ht.2 hab⟩
