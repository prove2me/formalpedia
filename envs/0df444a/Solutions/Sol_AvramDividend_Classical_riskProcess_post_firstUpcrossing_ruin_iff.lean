-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_post_firstUpcrossing_ruin_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:12:22.419142+00:00
-- url     : https://prove2.me/submissions/2f6cfc7c-836a-47b7-8b15-0d729efe7c2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_post_firstUpcrossing_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
      a + (X.X (u + t) ω - X.X u ω) <
        max 0
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X u ω) := by
  rw [AvramDividend.Classical.riskProcess_barrier_post_firstUpcrossing_shift
    X x a hxa u t ω hu hb]
  exact sub_lt_zero
