-- Prove2me | solution 1 for ErlerGross.kappaIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:24:31.997988+00:00
-- url     : https://prove2.me/submissions/2abf615c-fdd3-4d01-96f6-d68c65142de9

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_kappaIntegrand_norm_bound

open MeasureTheory

theorem solution : Integrable ErlerGross.kappaIntegrand := by
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 := by
    norm_num [Module.finrank_self]
  apply (integrable_one_add_norm (E := ℝ) hdim).mono'
  · change AEStronglyMeasurable (fun κ : ℝ =>
      (1 - Real.cosh (Real.pi * κ / 2)) / (1 + 2 * Real.cosh (Real.pi * κ / 2)) *
        (1 / (2 * κ * Real.sinh (Real.pi * κ / 2)))) volume
    fun_prop
  · exact Filter.Eventually.of_forall fun κ => by
      simpa only [Real.norm_eq_abs] using ErlerGross.kappaIntegrand_norm_bound κ
