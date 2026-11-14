-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a65_original_discounted_zerojump_stopmask_generator_variance_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:15.291426+00:00
-- url     : https://prove2.me/submissions/50e90e7d-89b3-4667-bb32-2404f818ab13

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a64_original_zerojump_discounted_generator_variance_drift_cancellation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original Gaussian stop-masked physical grid generator and quadratic compensator cancel exactly to the source drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range m, if s i < ρ ω then
        E (s i) * (iteratedDeriv 2 w (Y (s i)) / 2 * ((Δ : ℝ) * X.σ ^ 2)) -
          (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
      else 0) =
    (∑ i ∈ Finset.range m, if s i < ρ ω then
      -((Δ : ℝ) * E (s i) * X.c * deriv w (Y (s i)))
    else 0) := by
  dsimp
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω
  · simp only [if_pos h]
    exact avram_ga_a64_original_zerojump_discounted_generator_variance_drift_cancellation
      X hν x D w q ω
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
  · simp only [if_neg h]
