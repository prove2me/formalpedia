-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_ratio_monotone_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:04:53.630848+00:00
-- url     : https://prove2.me/submissions/bf708dcf-153b-438b-b63e-c1ac698e386e

import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Raising initial capital increases the canonical scale ratio at fixed barrier. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x y : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    W x / W a ≤ W y / W a := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hWxy : W x ≤ W y :=
    hW.2.2.2.1 (Set.mem_Ici.mpr hx0) (Set.mem_Ici.mpr hy0) hxy
  exact div_le_div_of_nonneg_right hWxy (le_of_lt hWa)
