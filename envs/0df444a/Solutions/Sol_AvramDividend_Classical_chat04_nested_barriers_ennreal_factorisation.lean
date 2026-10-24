-- Prove2me | solution 1 for AvramDividend.Classical.chat04_nested_barriers_ennreal_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:38:23.191309+00:00
-- url     : https://prove2.me/submissions/1c99e3c3-71d8-4a95-ba81-8307876b2f06

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_chat04_nested_barriers_scale_exit_factorisation
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Nested scale factors multiply in the valuation domain ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a b : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha : 0 < a) (hab : a ≤ b) :
    ENNReal.ofReal (W x / W b) =
      ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / W b) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hratio : 0 ≤ W x / W a := div_nonneg hWx hWa.le
  calc
    ENNReal.ofReal (W x / W b) =
      ENNReal.ofReal ((W x / W a) * (W a / W b)) := by
        exact congrArg ENNReal.ofReal
          (chat04_nested_barriers_scale_exit_factorisation
            X hX q hq W hW x a b hx0 hxa ha hab)
    _ = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / W b) :=
      ENNReal.ofReal_mul hratio
