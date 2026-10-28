-- Prove2me | solution 18 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:38:42.661877+00:00
-- url     : https://prove2.me/submissions/b4f5d1b5-ea56-4333-8a20-90c744ea3426
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
Assigned-unit reduction for `barrierStrategy_zero_boundary_value_identity` (c292):
Proved `barrierValue_self_eq_barrierSupValue` (11b589b7) at `a = 0` supplies the
dividend-to-supValue identity; Open `zero_reflectedSupValue_eq_barrierValue`
(b83a725b, verbatim binders X hX q hq W hW) closes the reflected-to-scale leg.
Transitivity gives the zero-boundary identity. At best SKETCH_ACCEPTED until
b83a is proved. Prepared 2026-10-28.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  have h1 :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q 0
  have h2 :=
    AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
  exact h1.trans h2
