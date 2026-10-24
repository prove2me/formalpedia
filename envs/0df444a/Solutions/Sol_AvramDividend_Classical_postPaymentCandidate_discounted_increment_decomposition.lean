-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentCandidate_discounted_increment_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:38:15.961153+00:00
-- url     : https://prove2.me/submissions/4e00c16e-7035-48f3-a91d-507b7e02b9a4

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Discrete discounted product rule for the verification function evaluated
    on the post-payment càdlàg reserve; no regularity assumptions on w. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    Real.exp (-(q * (t : ℝ))) *
      w (x + X.X t ω - rightLimit D t ω) -
    Real.exp (-(q * (s : ℝ))) *
      w (x + X.X s ω - rightLimit D s ω) =
    Real.exp (-(q * (t : ℝ))) *
      (w (x + X.X t ω - rightLimit D t ω) -
       w (x + X.X s ω - rightLimit D s ω)) +
    (Real.exp (-(q * (t : ℝ))) -
       Real.exp (-(q * (s : ℝ)))) *
      w (x + X.X s ω - rightLimit D s ω) := by
  ring
