-- Prove2me | solution 1 for ConnesGreen.RG0Integration.weil_nonnegative_at_window_of_all_smaller_windows
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:39:16.925096+00:00
-- url     : https://prove2.me/submissions/7418941d-3184-40d3-9a68-1e895cbd2a0e

import Theorems.Thm_ConnesGreen_supported_test_fits_smaller_window
import Definitions.Def_ConnesGreen_canonical_model
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section


theorem solution (c : ℝ) (hc : 0 < c)
    (hsmall : ∀ t : ℝ, 0 < t → t < c → ∀ g : ℝ → ℂ, SupportedTest t g →
      0 ≤ (weilDistribution (conv g (starInv g))).re) :
    ∀ g : ℝ → ℂ, SupportedTest c g → 0 ≤ (weilDistribution (conv g (starInv g))).re := by
  intro g hg
  obtain ⟨t, ht, htc, hgt⟩ := supported_test_fits_smaller_window c hc g hg
  exact hsmall t ht htc g hgt
