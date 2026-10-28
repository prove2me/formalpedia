-- Prove2me | solution 4 for AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:41:03.626219+00:00
-- url     : https://prove2.me/submissions/2cc6c828-3257-42f1-bf96-8fad76434f70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_standing_bounded_variation
import Theorems.Thm_AvramDividend_Classical_zero_barrier_instant_ruin_of_standing_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
Authoritative DECOMP0/1 case split for `zero_reflectedSupValue_eq_barrierValue`:
BoundedVariation leg via Open 7daa (verbatim binders + hBV); unbounded leg via
Open 8bec instant ruin (X hX hnbv) fed to Proved 87b3 (X q hq W hW hnbv hRuin).
At best SKETCH_ACCEPTED until 7daa + 8bec are proved; unblocks 9e8e/c292.
Prepared 2026-10-28.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  by_cases hBV : X.BoundedVariation
  · exact AvramDividend.Classical.zero_reflectedSupValue_of_standing_bounded_variation
      X hX q hq W hW hBV
  · exact AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_instant_ruin
      X q hq W hW hBV
      (AvramDividend.Classical.zero_barrier_instant_ruin_of_standing_unbounded_variation X hX hBV)
