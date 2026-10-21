-- Prove2me | solution 2 for GaussianMatrix.wishart_lambda_min_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T05:49:45.722476+00:00
-- url     : https://prove2.me/submissions/5a9181ca-2c09-4110-94d4-cb9d7992a8c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_wishart_lambda_min_cdf_density_bound
import Theorems.Thm_GaussianMatrix_density_integral_le_tail_bound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
          * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
  have h1 := wishart_lambda_min_cdf_density_bound hr hrk t ht
  have h2 := density_integral_le_tail_bound hr hrk ht
  exact h1.trans h2
