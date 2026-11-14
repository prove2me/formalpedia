-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a60_original_stopped_postpayment_spatial_increment_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:18.459106+00:00
-- url     : https://prove2.me/submissions/0dd8edb6-ce54-4cd0-8bda-44a004324321

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The actual original stopped Gaussian frozen-dividend source spatial displacement is exactly its genuine Lévy increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 -> Ω -> ℝ)
    (n m i : Nat) (ρ : Ω -> ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : Nat -> ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (ρ ω)
    let Y : ℝ := x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℝ := x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    Z - Y = X.X (v (i + 1)) ω - X.X (v i) ω := by
  dsimp
  ring
