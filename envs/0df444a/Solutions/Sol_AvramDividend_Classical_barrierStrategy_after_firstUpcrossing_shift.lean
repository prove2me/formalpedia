-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:56:34.866278+00:00
-- url     : https://prove2.me/submissions/a68fa61e-9a5f-4136-bb41-6613e7636ef8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_attained_threshold_shift
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
    barrierStrategy X x a (u + t) ω =
      max 0
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X u ω) := by
  obtain ⟨hlevel, hpeak⟩ :=
    AvramDividend.Classical.firstUpcrossing_attains_peak
      X (a - x) (sub_nonneg.mpr hxa) ω u hu
  exact AvramDividend.Classical.barrierStrategy_after_attained_threshold_shift
    X x a hxa u t ω hb hpeak hlevel
