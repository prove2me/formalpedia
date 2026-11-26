-- Prove2me | solution 1 for Eden.planar_factors_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:05.843441+00:00
-- url     : https://prove2.me/submissions/5d0f6046-99e3-45d4-ad01-450a6a01322c

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_log_planar_factors
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_radialAmplitude_pos


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    radialAmplitude t s * planarAmplitude t s = Real.exp (2 * t - 6 * radialDefect t s) := by
  rw [← log_planar_factors ht hs, Real.exp_add,
    Real.exp_log (radialAmplitude_pos ht hs), Real.exp_log (planarAmplitude_pos ht hs)]
end Eden
