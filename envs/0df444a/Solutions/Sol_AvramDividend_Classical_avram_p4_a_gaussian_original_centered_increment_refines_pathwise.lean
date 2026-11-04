-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_centered_increment_refines_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:35.790179+00:00
-- url     : https://prove2.me/submissions/d56ddba8-b698-406c-8607-faf2f8f4cb72

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original-jump-subtracted Gaussian residual admits pathwise
refinement at arbitrary random clocks. This is an algebraic identity, with
no Brownian construction, stopping-time or path-regularity assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (s u t : Ω → ℝ≥0) :
    let Z : ℝ≥0 → Ω → ℝ := fun r ω =>
      X.X r ω - (r : ℝ) * X.c - Jsmall r ω - Jlarge r ω
    ∀ ω, Z (t ω) ω - Z (s ω) ω =
      (Z (u ω) ω - Z (s ω) ω) +
      (Z (t ω) ω - Z (u ω) ω) := by
  intro ω
  ring
  intro ω
  trivial
