-- Prove2me | solution 9 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:51:59.127429+00:00
-- url     : https://prove2.me/submissions/4ca8b2b3-e614-41fc-a012-730d2118e83c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Authoritative DEC0 route for `zero_cap_value_at_zero_upper_bound` (c785):
Open 9e8e88ea (barrier_zero_boundary_value, verbatim binders) supplies hboundary;
Proved d58a54f2 turns that boundary identity into the cap-value upper bound.
At best SKETCH_ACCEPTED until 9e8e is proved; advances the zero-cap leg toward the barrier root.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  have hB := barrier_zero_boundary_value X hX q hq W hW
  exact zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hB
