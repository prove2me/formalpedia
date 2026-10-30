-- Prove2me | solution 6 for AvramDividend.Classical.barrier_boundary_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:54:03.363018+00:00
-- url     : https://prove2.me/submissions/4ce84222-fb28-459f-b0e8-ddbb5e6defaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Boundary value via Proved self-bridge + Open supValue ratio.
-- Variant r (2026-10-29): rewrite architecture over the prior calc file.
-- hself identifies the barrier dividend with the sup value (Proved 11b589b7);
-- hsup identifies the sup value with the scale ratio (Open a8d4c941).
-- Two sequential rewrites replace the calc chain; mathematics unchanged.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    dividendValue X q a (barrierStrategy X a a) = ENNReal.ofReal (W a / deriv W a) := by
  have hself :
      dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  have hsup :
      barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrierSupValue_eq_scale_ratio
      X hX q hq W hW a ha
  rw [hself]
  rw [hsup]
