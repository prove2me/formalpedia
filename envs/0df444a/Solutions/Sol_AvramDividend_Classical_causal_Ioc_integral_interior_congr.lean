-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_integral_interior_congr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:51:30.407977+00:00
-- url     : https://prove2.me/submissions/db61a7a1-0870-40f3-86e2-75a017a41bf3

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Endpoints of real Lebesgue intervals do not affect causal integrals. -/
theorem solution
    (f g : ℝ → ℝ) (x : ℝ)
    (hfg : ∀ s : ℝ, 0 < s → s < x → f s = g s) :
    (∫ s in Ioc (0 : ℝ) x, f s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, g s ∂volume) := by
  simp only [integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hfg s hs.1 hs.2
