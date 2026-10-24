-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_increment_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:30:36.718153+00:00
-- url     : https://prove2.me/submissions/8671fc24-0f05-4030-8ba8-cedf8bfa8e38

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The càdlàg post-payment controlled reserve increment is the Lévy
    increment minus the corresponding full Stieltjes-control increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    (x + X.X t ω - rightLimit D t ω) -
      (x + X.X s ω - rightLimit D s ω) =
    (X.X t ω - X.X s ω) -
      (rightLimit D t ω - rightLimit D s ω) := by
  ring
