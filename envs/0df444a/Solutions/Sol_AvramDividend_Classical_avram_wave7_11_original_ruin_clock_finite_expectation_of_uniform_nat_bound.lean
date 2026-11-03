-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_ruin_clock_finite_expectation_of_uniform_nat_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:37:54.234073+00:00
-- url     : https://prove2.me/submissions/85975bae-612e-496d-ba97-f3d7739b4d8a

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A finite real uniform natural-clock bound makes the original full-ruin
    finite-horizon expected discounted Stieltjes dividend finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T B : ℝ)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) < ⊤ := by
  exact lt_of_le_of_lt
    (avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
      X x D hD q T (ENNReal.ofReal B) hBound)
    ENNReal.ofReal_lt_top
