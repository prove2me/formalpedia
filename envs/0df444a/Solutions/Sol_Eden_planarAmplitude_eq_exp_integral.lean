-- Prove2me | solution 1 for Eden.planarAmplitude_eq_exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:59.555413+00:00
-- url     : https://prove2.me/submissions/eba8f038-383c-46c1-82f3-54f5e94f3935

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Eden_GrowthRates
import Theorems.Thm_Eden_log_planarAmplitude_eq_integral
import Theorems.Thm_Eden_planarAmplitude_pos


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s)) := by
  rw [← log_planarAmplitude_eq_integral ht hs, Real.exp_log (planarAmplitude_pos ht hs)]
end Eden
