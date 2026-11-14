-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a62_positive_gaussian_chernoff_optimal_mesh_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:13.47394+00:00
-- url     : https://prove2.me/submissions/87f16b31-3a1c-420b-90bf-d51b9effec0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Optimising the Gaussian positive exponential Chernoff tilt at an actual positive mesh variance. -/
theorem solution (d θ δ : ℝ) (hd : 0 < d)
    (hThreshold : θ * d ≤ δ) :
    0 ≤ δ / d - θ ∧
      Real.exp (-(δ / d - θ) * δ +
        d * (θ + (δ / d - θ))^2 / 2) =
      Real.exp (θ * δ - δ^2 / (2 * d)) := by
  constructor
  · exact sub_nonneg.mpr ((le_div_iff₀ hd).2 hThreshold)
  · congr 1
    field_simp [ne_of_gt hd]
    ring
