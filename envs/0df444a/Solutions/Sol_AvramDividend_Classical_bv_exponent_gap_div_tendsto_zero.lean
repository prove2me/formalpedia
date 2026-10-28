-- Prove2me | solution 1 for AvramDividend.Classical.bv_exponent_gap_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:21:08.393292+00:00
-- url     : https://prove2.me/submissions/bcf6db72-1434-43f5-b691-9391bd9dea04

import Theorems.Thm_AvramDividend_Classical_negative_jump_full_normalized_exp_deficit_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Tendsto

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    Tendsto (fun θ : ℝ => (X.drift * θ - X.ψ θ) / θ)
      atTop (nhds (0 : ℝ)) := by
  have h := negative_jump_full_normalized_exp_deficit_tendsto_zero X.ν
    (chat07_bv_negative_jump_min_abs_integrable X hBV)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with θ hθ
  rw [bv_exponent_negative_jump_deficit_exact X hBV θ hθ, integral_div]
