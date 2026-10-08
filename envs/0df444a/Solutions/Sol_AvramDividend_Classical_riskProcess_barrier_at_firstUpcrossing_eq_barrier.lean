-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_barrier_at_firstUpcrossing_eq_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:51:31.799854+00:00
-- url     : https://prove2.me/submissions/095710a1-6cae-4beb-b302-7e5d38af1746

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
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
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞))) :
    riskProcess X x (barrierStrategy X x a) u ω = a := by
  have hb : 0 ≤ a - x := sub_nonneg.mpr hxa
  have hhit : X.X u ω = a - x :=
    AvramDividend.Classical.firstUpcrossing_value_eq_threshold
      X (a - x) hb ω u hu
  have hbelow : ∀ s : ℝ≥0, s ≤ u → X.X s ω ≤ a - x := by
    intro s hs
    rcases lt_or_eq_of_le hs with hlt | heq
    · exact AvramDividend.Classical.firstUpcrossing_prethreshold_le
        X (a - x) ω u hu s hlt
    · simpa only [heq, hhit] using le_refl (a - x)
  have hdiv : barrierStrategy X x a u ω = 0 :=
    AvramDividend.Classical.barrierStrategy_zero_before_upcrossing
      X x a u ω hbelow
  change x + X.X u ω - barrierStrategy X x a u ω = a
  rw [hhit, hdiv]
  ring
