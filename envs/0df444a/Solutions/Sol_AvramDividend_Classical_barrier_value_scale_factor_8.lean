-- Prove2me | solution 8 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:57:16.797977+00:00
-- url     : https://prove2.me/submissions/e91c09f9-05c3-416b-b932-372944d12ce0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := by
  -- Principal route: positivity is the Proved scale-function fact;
  -- the product identity is the exit-factor identity at x and at a.
  -- Depends on Open 870df5c1, so at most a sketch until that leg is Proved.
  have hWpos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hexit_x :
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
      X hX q hq W hW a ha x hx0 hxa
  have hexit_a :
      dividendValue X q a (barrierStrategy X a a) =
        ENNReal.ofReal (W a / W a) * barrierSupValue X a q :=
    AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
      X hX q hq W hW a ha a (le_of_lt ha) le_rfl
  have hWaa : W a / W a = 1 := div_self (ne_of_gt hWpos)
  have hsup : dividendValue X q a (barrierStrategy X a a) =
      barrierSupValue X a q := by
    rw [hexit_a, hWaa, ENNReal.ofReal_one, one_mul]
  refine ⟨hWpos, ?_⟩
  rw [hexit_x, ← hsup]
