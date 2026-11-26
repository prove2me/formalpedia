-- Prove2me | solution 1 for Eden.radialAmplitude_eq_exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:07.203809+00:00
-- url     : https://prove2.me/submissions/52dfa301-b7a3-4ad3-9ea5-a3ca336d2273

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
import Theorems.Thm_Eden_log_radialAmplitude_eq_integral
import Theorems.Thm_Eden_radialAmplitude_pos


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by
  rw [← log_radialAmplitude_eq_integral ht hs, Real.exp_log (radialAmplitude_pos ht hs)]
end Eden
