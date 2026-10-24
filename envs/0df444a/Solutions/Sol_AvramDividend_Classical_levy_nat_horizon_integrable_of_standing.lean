-- Prove2me | solution 1 for AvramDividend.Classical.levy_nat_horizon_integrable_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:56:59.268158+00:00
-- url     : https://prove2.me/submissions/83c09e52-5dcd-48a4-978d-8f55e2acc656

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Standing integrability at unit time propagates to integer horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ n : ℕ, Integrable (X.X (n : ℝ≥0)) P := by
  haveI : IsProbabilityMeasure P := X.isProbability
  intro n
  induction n with
  | zero =>
      have hz : X.X (0 : ℝ≥0) = fun _ : Ω => (0 : ℝ) :=
        funext X.X_zero
      simpa only [Nat.cast_zero, hz] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
  | succ n ih =>
      have hle : (n : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := by
        exact_mod_cast Nat.le_succ n
      have hDist : IdentDistrib
          (fun ω => X.X ((n + 1 : ℕ) : ℝ≥0) ω - X.X (n : ℝ≥0) ω)
          (X.X 1) P P := by
        simpa [Nat.cast_add] using
          (X.stationaryIncrements (n : ℝ≥0) ((n + 1 : ℕ) : ℝ≥0) hle)
      have hInc : Integrable
          (fun ω => X.X ((n + 1 : ℕ) : ℝ≥0) ω - X.X (n : ℝ≥0) ω) P :=
        hDist.integrable_iff.mpr hX.2.1
      have hTotal := hInc.add ih
      have hFunction :
          (fun ω => X.X ((n + 1 : ℕ) : ℝ≥0) ω - X.X (n : ℝ≥0) ω) +
              X.X (n : ℝ≥0) = X.X ((n + 1 : ℕ) : ℝ≥0) := by
        funext ω
        exact sub_add_cancel _ _
      rw [hFunction] at hTotal
      exact hTotal
