-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_two_horizon_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:07:57.194328+00:00
-- url     : https://prove2.me/submissions/131a2f47-27b6-455c-9378-8036f9d67da8

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Future two-horizon Lévy increments telescope pathwise at any random time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (h k : ℝ≥0) (ω : Ω) :
    X.X (τ ω + (h + k)) ω - X.X (τ ω) ω =
      (X.X (τ ω + (h + k)) ω - X.X (τ ω + h) ω) +
        (X.X (τ ω + h) ω - X.X (τ ω) ω) := by
  ring
