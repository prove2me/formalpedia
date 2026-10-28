-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_canonical_esscher_density_eq_displacement_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:19:21.337451+00:00
-- url     : https://prove2.me/submissions/7c4ba345-26fb-49c1-b2f7-eafebc0409a8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Zero-start Lévy paths identify the displacement form of the
finite-terminal Esscher tilt with the canonical terminal-level form. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (T : ℝ≥0) :
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X T ω - X.X 0 ω) -
        (T : ℝ) * X.ψ θ))) =
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))) := by
  have heq :
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X T ω - X.X 0 ω) -
          (T : ℝ) * X.ψ θ))) =
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))) := by
    funext ω
    rw [X.X_zero ω]
    simp
  rw [heq]
