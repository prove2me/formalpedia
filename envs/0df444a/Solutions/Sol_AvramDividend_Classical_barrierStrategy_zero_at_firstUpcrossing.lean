-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_at_firstUpcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:44:08.038041+00:00
-- url     : https://prove2.me/submissions/23ba1ecc-04ca-4a15-9472-0b4ddd7d7f4e

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
    barrierStrategy X x a u ω = 0 := by
  have hb : 0 ≤ a - x := sub_nonneg.mpr hxa
  have hat : X.X u ω = a - x :=
    AvramDividend.Classical.firstUpcrossing_value_eq_threshold
      X (a - x) hb ω u hu
  apply AvramDividend.Classical.barrierStrategy_zero_before_upcrossing X x a u ω
  intro s hs
  rcases lt_or_eq_of_le hs with hlt | heq
  · exact AvramDividend.Classical.firstUpcrossing_prethreshold_le
      X (a - x) ω u hu s hlt
  · simpa only [heq, hat] using le_refl (a - x)
