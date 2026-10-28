-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_firstRecord_drawdown_at_observation_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:45:40.754865+00:00
-- url     : https://prove2.me/submissions/d2f0d2e5-85cf-4241-89b1-d330e9712bd1

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At the actual observation clock after an attained first strict upper
record, the reflected drawdown is determined by the shifted future path
over exactly the residual interval, including the endpoint tie u=e. -/
theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (e : Θ → ℝ≥0) (η : Θ) (hObs : u ≤ e η) :
    runningSup X (e η) ω - X.X (e η) ω =
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 (e η - u)) -
        X.X (e η) ω := by
  have hReset :=
    firstRecord_drawdown_post_shift_reset X b hb ω u hu hBdd (e η - u)
  simpa only [add_tsub_cancel_of_le hObs] using hReset
