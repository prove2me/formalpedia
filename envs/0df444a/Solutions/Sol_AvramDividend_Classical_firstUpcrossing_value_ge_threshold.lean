-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_value_ge_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:38:45.410828+00:00
-- url     : https://prove2.me/submissions/3922a078-63cd-4b57-9ef9-514667dda8e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_le_value

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
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    b ≤ X.X u ω := by
  exact AvramDividend.Classical.firstUpcrossing_threshold_le_value
    X b hb ω u hu
