-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_value_le_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:53:53.522467+00:00
-- url     : https://prove2.me/submissions/98bd5c66-52bf-41ab-b76f-92abaee121cb

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! No-positive-jump endpoint bound from the strict first-passage prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    X.X u ω ≤ b := by
  apply AvramDividend.Classical.path_value_le_of_strict_prefix_le X b hb ω u
  exact AvramDividend.Classical.firstUpcrossing_prethreshold_le X b ω u hu
