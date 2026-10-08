-- Prove2me | solution 1 for AvramDividend.Classical.levy_laplace_exponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:08:02.803614+00:00
-- url     : https://prove2.me/submissions/f0875f51-92f7-40d0-91b1-8acdb35934a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact source Lévy–Khintchine exponent is zero at the origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) : X.ψ 0 = 0 := by
  simp [SpectrallyNegativeLevy.ψ, laplaceExponent]
