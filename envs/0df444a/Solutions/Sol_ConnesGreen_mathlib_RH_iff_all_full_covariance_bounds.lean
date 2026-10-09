-- Prove2me | solution 1 for ConnesGreen.mathlib_RH_iff_all_full_covariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T17:20:52.723011+00:00
-- url     : https://prove2.me/submissions/4cabb5ff-08bc-483c-9544-2a7c3ab649b0

import Theorems.Thm_ConnesGreen_weilPositive_iff_all_full_covariance_bounds
import Theorems.Thm_ConnesRZFrontier_weilPositive_iff_mathlib_RH
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem solution :
    RiemannHypothesis ↔ ∀ t : ℝ, ∀ ht : 0 < t,
      canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint ≤
        canonicalPositiveCovariance t ht :=
  ConnesRZFrontier.weilPositive_iff_mathlib_RH.symm.trans
    ConnesGreen.weilPositive_iff_all_full_covariance_bounds
