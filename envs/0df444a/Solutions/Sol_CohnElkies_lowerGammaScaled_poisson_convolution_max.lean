-- Prove2me | solution 1 for CohnElkies.lowerGammaScaled_poisson_convolution_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/9d4c3770-49a5-414b-ab10-ff7b0704260c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCapped_poisson_convolution_max
import Theorems.Thm_CohnElkies_lowerGammaScaledCapped_poisson_tendsto

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
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2)
          (c * Real.sqrt d) (((d : ℝ) / 2) * Y) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  exact le_of_tendsto_of_tendsto
    (lowerGammaScaledCapped_poisson_tendsto
      (c := c) hdpos hbelow habove s)
    (lowerGammaScaledCapped_poisson_tendsto
      (c := c) hdpos hbelow habove 0)
    (Filter.Eventually.of_forall (fun n : ℕ =>
      lowerGammaScaledCapped_poisson_convolution_max
        (D := (n : ℝ)) hd hc hbelow habove s))
end CohnElkies
