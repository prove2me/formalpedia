-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_barrier_post_firstUpcrossing_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:05:37.391746+00:00
-- url     : https://prove2.me/submissions/df1f4e6f-1297-4f9c-b9aa-8e8dcdcfcd21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift

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
    riskProcess X x (barrierStrategy X x a) (u + t) ω =
      a + (X.X (u + t) ω - X.X u ω) -
        max 0
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X u ω) := by
  have hlevel : X.X u ω = a - x :=
    AvramDividend.Classical.firstUpcrossing_value_eq_threshold
      X (a - x) (sub_nonneg.mpr hxa) ω u hu
  have hshift :
      barrierStrategy X x a (u + t) ω =
        max 0
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
            X.X u ω) :=
    AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_shift
      X x a hxa u t ω hu hb
  change x + X.X (u + t) ω - barrierStrategy X x a (u + t) ω = _
  rw [hshift]
  rw [hlevel]
  ring
