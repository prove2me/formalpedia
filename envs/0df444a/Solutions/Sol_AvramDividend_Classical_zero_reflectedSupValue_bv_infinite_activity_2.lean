-- Prove2me | solution 2 for AvramDividend.Classical.zero_reflectedSupValue_bv_infinite_activity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:49:21.389432+00:00
-- url     : https://prove2.me/submissions/176b3744-c15b-4997-b7a0-74a9a13789f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_scale_derivZeroPlus_top_of_bv_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Authoritative DEC1 route for `zero_reflectedSupValue_bv_infinite_activity` (625fac59):
Open ff758fb4 supplies a.e. early downward jumps from hInfinite;
Proved 0893ca6f supplies derivZeroPlus W = ⊤ from the full BV+Standing context;
Proved 9228cae3 closes the reflected value from jumps + slope.
At best SKETCH_ACCEPTED until ff758fb4 is proved; unblocks 7daa -> b83a -> 9e8e/c292.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  have hJumps :=
    ae_early_downward_jumps_of_infinite_negative_activity X hInfinite
  have hder :=
    scale_derivZeroPlus_top_of_bv_infinite_negative_activity
      X hX q hq W hW hBV hInfinite
  exact zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
    X q W hJumps hder
