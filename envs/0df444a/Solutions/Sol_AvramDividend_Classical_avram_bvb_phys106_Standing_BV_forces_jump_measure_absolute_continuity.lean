-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys106_Standing_BV_forces_jump_measure_absolute_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:19:49.860401+00:00
-- url     : https://prove2.me/submissions/60936ba6-2ab3-4bcf-8cc9-5ceedfe270eb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The paper's Condition (3.3) eliminates atoms of the jump measure
in the bounded-variation case: the Lévy measure is absolutely continuous. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    X.ν ≪ (volume : Measure ℝ) := by
  exact standing_bv_levy_absolutely_continuous X hStanding hBV
