-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_rightdividend_terminal_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:58:39.308869+00:00
-- url     : https://prove2.me/submissions/14491fe4-8704-449d-b59e-a39d2d714dec

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- A right dividend at the original stopping boundary is paid from the
pre-rightpayment reserve and leaves precisely the post-rightpayment reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hjump :
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) :
    rightLimit D t ω - D t ω +
      w (x + X.X t ω - rightLimit D t ω) ≤
        w (riskProcess X x D t ω) := by
  have hreserve :
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) =
        x + X.X t ω - rightLimit D t ω := by
    simp only [riskProcess]
    ring
  rw [hreserve] at hjump
  linarith
