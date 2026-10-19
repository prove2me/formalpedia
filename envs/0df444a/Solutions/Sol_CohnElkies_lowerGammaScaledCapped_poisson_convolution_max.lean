-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCapped_poisson_convolution_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/ce001725-9533-4174-a62c-4cb73fb7d6db

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedLowerClip_poisson_convolution_max
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedLowerClip_poisson_tendsto

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
    {d : ℕ} (hd : 2 ≤ d) {c D σ : ℝ}
    (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaBoundaryCapped ((d : ℝ) / 2)
        (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) D (((d : ℝ) / 2) * Y) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  exact le_of_tendsto_of_tendsto
    (lowerGammaScaledCappedLowerClip_poisson_tendsto
      hdpos hbelow habove s)
    (lowerGammaScaledCappedLowerClip_poisson_tendsto
      hdpos hbelow habove 0)
    (Filter.Eventually.of_forall (fun n : ℕ =>
      lowerGammaScaledCappedLowerClip_poisson_convolution_max
        hd hc (Nat.cast_nonneg n) hbelow habove s))
end CohnElkies
