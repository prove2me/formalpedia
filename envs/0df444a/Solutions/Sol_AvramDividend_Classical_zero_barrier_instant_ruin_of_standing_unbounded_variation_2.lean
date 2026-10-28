-- Prove2me | solution 2 for AvramDividend.Classical.zero_barrier_instant_ruin_of_standing_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:46:29.95298+00:00
-- url     : https://prove2.me/submissions/2e1922fd-97ef-4c42-bd0c-ff3c7c16d9d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Authoritative route for `zero_barrier_instant_ruin_of_standing_unbounded_variation` (8bec):
Open 703dc740 supplies the a.e. near-zero negative path (binders X hnbv, no Standing needed);
Proved 092db474 turns each such path into `barrierRuinTime X 0 ω = 0`.
At best SKETCH_ACCEPTED until 703dc740 is proved; unblocks b83a UBV leg and hence 9e8e/c292.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 := by
  have hAe := ae_negative_near_zero_of_unbounded_variation X hnbv
  exact hAe.mono fun ω hNeg =>
    barrierRuinTime_zero_of_near_zero_negative_path X ω hNeg
