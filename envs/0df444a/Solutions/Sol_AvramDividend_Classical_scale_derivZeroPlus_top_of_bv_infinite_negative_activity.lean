-- Prove2me | solution 1 for AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:14:44.451272+00:00
-- url     : https://prove2.me/submissions/68ba1a2b-c033-4ec2-933e-32f5c9680640

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Theorems.Thm_AvramDividend_Classical_bv_scale_deriv_ge_negative_jump_tail
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The Lévy-tail lower bound makes the zero-right scale derivative infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    derivZeroPlus W = ⊤ := by
  have hνinf : X.ν (Iio (0 : ℝ)) = ⊤ :=
    top_unique (le_of_not_gt hInfinite)
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hd2 : 0 < X.drift ^ 2 := sq_pos_of_pos hd
  have htail := negative_jump_real_tail_tendsto_top X.ν X.ν_integrable hνinf
  apply derivZeroPlus_eq_top_of_right_tendsto_atTop
  refine tendsto_atTop.2 ?_
  intro B
  have hev := (tendsto_atTop.1 htail) (B * X.drift ^ 2)
  filter_upwards [hev, self_mem_nhdsWithin] with x hxmass hxpos
  have hbound :=
    bv_scale_deriv_ge_negative_jump_tail X hX q hq W hW hBV x hxpos
  have hdiv : B ≤ (X.ν (Iio (-x))).toReal / X.drift ^ 2 := by
    apply (le_div_iff₀ hd2).2
    exact hxmass
  exact hdiv.trans hbound
