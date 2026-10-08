-- Prove2me | solution 1 for ConnesGreen.RG0Integration.total_covariance_le_of_original_quadratic_shift
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:42:59.65836+00:00
-- url     : https://prove2.me/submissions/d2f07542-cb75-4a9e-9837-88b81e87d298

import Theorems.Thm_WeilDefect_MarkerStability_covariance_le_regularized_of_quadratic_shift
import Definitions.Def_ConnesGreen_RG0_original_actors
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section


theorem solution (t : ℝ) (ht : 0 < t)
    (k ε : ℝ) (hkε : k ≤ ε)
    (hbound : ∀ x : Physical t, -k * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalNegativeSynthesis t ht).adjoint x‖ ^ 2) :
    canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint ≤
      canonicalPositiveCovariance t ht + ε • 1 := by
  apply covariance_le_regularized_of_quadratic_shift _
    (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis t ht)).isSelfAdjoint
    _ k ε hkε
  intro x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  change -k * ‖x‖ ^ 2 ≤ RCLike.re ⟪(canonicalPositiveSynthesis t ht ∘L
    (canonicalPositiveSynthesis t ht).adjoint) x, x⟫_ℂ - _
  rw [← hp]
  exact hbound x
