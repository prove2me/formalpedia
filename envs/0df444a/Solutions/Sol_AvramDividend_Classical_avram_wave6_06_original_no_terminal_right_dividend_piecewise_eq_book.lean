-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:35:04.224174+00:00
-- url     : https://prove2.me/submissions/a05457dc-0be0-41d3-9deb-c86beff0d221

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hNoAtom : ∀ ω, rightLimit D (τ ω) ω = D (τ ω) ω) :
    ∀ ω, W ω = riskProcess X x D (τ ω) ω := by
  intro ω
  rw [hW ω]
  by_cases hpre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · simp [hpre, riskProcess, hNoAtom ω]
  · simp [hpre]
