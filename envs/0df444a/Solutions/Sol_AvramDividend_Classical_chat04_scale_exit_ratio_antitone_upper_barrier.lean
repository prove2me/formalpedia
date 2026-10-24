-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_exit_ratio_antitone_upper_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:28:16.370797+00:00
-- url     : https://prove2.me/submissions/06b2226d-8558-412d-a292-798d360ea644

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

/-- Scale exit factor decreases when the upper barrier increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a b : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha : 0 < a) (hab : a ≤ b) :
    W x / W b ≤ W x / W a := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWb : 0 < W b :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW b (lt_of_lt_of_le ha hab)
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hWab : W a ≤ W b :=
    hW.2.2.2.1 (Set.mem_Ici.mpr (le_of_lt ha))
      (Set.mem_Ici.mpr (le_trans (le_of_lt ha) hab)) hab
  apply (div_le_div_iff₀ hWb hWa).2
  exact mul_le_mul_of_nonneg_left hWab hWx
