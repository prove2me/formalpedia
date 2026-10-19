-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedLowerClip_poisson_convolution_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/462cdcfd-5bc6-4d7a-a5b3-ad78b29d43d2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_poisson_convolution_max
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_integral_eq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c D n σ : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedLowerClip d c D n Y) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hplus := lowerGammaScaledCappedClipped_poisson_convolution_max
    (D := D) hd hc hn hbelow habove s
  rw [lowerGammaScaledCappedClipped_integral_eq
    hdpos hbelow habove s,
    lowerGammaScaledCappedClipped_integral_eq
      hdpos hbelow habove 0] at hplus
  linarith
end CohnElkies
