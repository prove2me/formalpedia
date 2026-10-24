-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_discounted_increment_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:33:43.655241+00:00
-- url     : https://prove2.me/submissions/809ec7c1-3fba-45f6-b942-bc234475893e

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact discounted-increment decomposition for a post-payment reserve,
    preserving the full right-limit dividend increment and both endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    Real.exp (-(q * (t : ℝ))) *
      (x + X.X t ω - rightLimit D t ω) -
    Real.exp (-(q * (s : ℝ))) *
      (x + X.X s ω - rightLimit D s ω) =
    Real.exp (-(q * (t : ℝ))) *
      ((X.X t ω - X.X s ω) -
        (rightLimit D t ω - rightLimit D s ω)) +
    (Real.exp (-(q * (t : ℝ))) -
       Real.exp (-(q * (s : ℝ)))) *
      (x + X.X s ω - rightLimit D s ω) := by
  ring
