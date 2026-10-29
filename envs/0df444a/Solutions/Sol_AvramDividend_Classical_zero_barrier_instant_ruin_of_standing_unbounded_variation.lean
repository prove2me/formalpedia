-- Prove2me | solution 1 for AvramDividend.Classical.zero_barrier_instant_ruin_of_standing_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:24:39.318994+00:00
-- url     : https://prove2.me/submissions/873017dc-1c46-4397-ba35-7b9937ff5222

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 := by
  exact (ae_negative_near_zero_of_unbounded_variation X hnbv).mono
    (fun ω hω => barrierRuinTime_zero_of_near_zero_negative_path X ω hω)
