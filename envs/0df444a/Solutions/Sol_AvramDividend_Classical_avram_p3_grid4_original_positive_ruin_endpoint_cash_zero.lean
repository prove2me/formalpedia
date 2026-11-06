-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_positive_ruin_endpoint_cash_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:08:38.258983+00:00
-- url     : https://prove2.me/submissions/953e79c4-5404-41c6-8c86-bbcb5c541a10

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : ℝ≥0)
    (hτ : 0 < τ)
    (hruin : (τ : ℝ≥0∞) = ruinTime X x D ω)
    (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ ({(τ : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
  exact avram_bv_env3_original_stopped_positive_horizon_atom_zero_without_strategy
    D ω (ruinTime X x D ω) τ hτ (le_of_eq hruin.symm) q
