-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_exponential_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:28:39.353994+00:00
-- url     : https://prove2.me/submissions/6a734602-2bc5-48fa-a96d-9485c4a1ecd2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) :
    Adapted 𝓕 (fun t ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) := by
  intro t
  exact ((measurable_const.mul (X.adapted t)).sub measurable_const).exp
