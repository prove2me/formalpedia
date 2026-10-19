-- Prove2me | solution 1 for CohnElkies.lowerStripPoissonMajorant_dimension_centered_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/5d6549de-78a3-4c81-85e8-4a2317b7245e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaled_poisson_convolution_max
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_scaled_convolution

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
    lowerStripPoissonMajorant ((d : ℝ) / 2)
      (c * Real.sqrt d) σ s ≤
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  rw [lowerStripPoissonMajorant_scaled_convolution
    hℓ (c * Real.sqrt d) σ s,
    lowerStripPoissonMajorant_scaled_convolution
      hℓ (c * Real.sqrt d) σ 0]
  simp only [zero_div]
  exact lowerGammaScaled_poisson_convolution_max
    hd hc hbelow habove (s / ((d : ℝ) / 2))
end CohnElkies
