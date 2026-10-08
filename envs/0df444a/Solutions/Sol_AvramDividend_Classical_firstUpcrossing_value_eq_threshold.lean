-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_value_eq_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:13:57.117611+00:00
-- url     : https://prove2.me/submissions/a00d8f32-2891-4c79-ab82-22436e206f74

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_le_value
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le

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
    X.X u ω = b := by
  have hge : b ≤ X.X u ω :=
    AvramDividend.Classical.firstUpcrossing_threshold_le_value X b hb ω u hu
  have hpre : ∀ t : ℝ≥0, t < u → X.X t ω ≤ b :=
    AvramDividend.Classical.firstUpcrossing_prethreshold_le X b ω u hu
  have hle : X.X u ω ≤ b :=
    AvramDividend.Classical.path_value_le_of_strict_prefix_le X b hb ω u hpre
  exact le_antisymm hle hge
