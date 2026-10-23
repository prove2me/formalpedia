-- Prove2me | solution 1 for AvramDividend.Classical.chat03_discounted_scale_initial_expectation_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:10:52.743252+00:00
-- url     : https://prove2.me/submissions/0945f680-4ba0-4ce3-a496-242124ff5859

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-!
At the zero clock, the Lévy process starts at zero on every path.
Its own probability-measure instance therefore normalises the initial
discounted q-scale expectation to the deterministic scale value.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ)
    (clock : ℕ → ℝ≥0) (hclock0 : clock 0 = 0) :
    (∫ ω, Real.exp (-(q * (clock 0 : ℝ))) *
      W (x + X.X (clock 0) ω) ∂P) = W x := by
  letI : IsProbabilityMeasure P := X.isProbability
  simp [hclock0, X.X_zero]
