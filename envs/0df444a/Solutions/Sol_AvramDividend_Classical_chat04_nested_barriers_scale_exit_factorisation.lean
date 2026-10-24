-- Prove2me | solution 1 for AvramDividend.Classical.chat04_nested_barriers_scale_exit_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:27:33.528884+00:00
-- url     : https://prove2.me/submissions/2e570d7d-c653-4521-a9d4-b7cadcc20195

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact multiplicative consistency of scale exit factors across nested barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a b : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha : 0 < a) (hab : a ≤ b) :
    W x / W b = (W x / W a) * (W a / W b) := by
  have hWa : W a ≠ 0 := ne_of_gt
    (scaleFunction_strict_pos_of_standing X hX q hq W hW a ha)
  have hWb : W b ≠ 0 := ne_of_gt
    (scaleFunction_strict_pos_of_standing X hX q hq W hW b (lt_of_lt_of_le ha hab))
  field_simp [hWa, hWb] <;> ring
