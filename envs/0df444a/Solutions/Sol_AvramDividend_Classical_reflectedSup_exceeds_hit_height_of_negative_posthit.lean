-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_exceeds_hit_height_of_negative_posthit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:55:37.469761+00:00
-- url     : https://prove2.me/submissions/098a2007-9f7e-4812-aee4-b5d94001b9cb

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_exceeds_hit_height_of_local_negative_increments
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T ζ x : ℝ≥0) (hT : T < ζ)
    (hHit : reflectedSup X T ω = (x : ℝ))
    (hNeg : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X (T + s) ω < X.X T ω) :
    ∃ t : ℝ≥0, T ≤ t ∧ t < ζ ∧
      (x : ℝ) < reflectedSup X t ω := by
  have hS : Monotone (fun t : ℝ≥0 => runningSup X t ω) :=
    (runningSup_monotone_and_path_le X ω).1
  exact reflected_excursion_exceeds_hit_height_of_local_negative_increments
    (fun t : ℝ≥0 => runningSup X t ω)
    (fun t : ℝ≥0 => X.X t ω)
    T ζ x hT hS hHit hNeg
