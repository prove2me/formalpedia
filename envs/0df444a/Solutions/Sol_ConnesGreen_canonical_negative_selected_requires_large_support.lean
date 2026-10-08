-- Prove2me | solution 1 for ConnesGreen.canonical_negative_selected_requires_large_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:16:02.132272+00:00
-- url     : https://prove2.me/submissions/ea474210-a735-4683-a1dc-96173fa17b52

import Theorems.Thm_ConnesGreen_canonical_selected_covariance_le_small_support
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros) (x : Physical T)
    (hneg : ‖(canonicalPositiveSynthesis T hT).adjoint x‖ ^ 2 -
      ‖(canonicalSelectedSynthesis T hT S).adjoint x‖ ^ 2 < 0) : positiveSupportRadius < T  := by
  by_contra hn
  have hb := (ContinuousLinearMap.le_def _ _).mp
    (ConnesGreen.canonical_selected_covariance_le_small_support T hT (le_of_not_gt hn) S)
  have hx := hb.re_inner_nonneg_left x
  have hp := (canonicalPositiveSynthesis T hT).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hm := (canonicalSelectedSynthesis T hT S).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp hm
  change 0 ≤ RCLike.re ⟪((canonicalPositiveSynthesis T hT ∘L (canonicalPositiveSynthesis T hT).adjoint) -
    (canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint)) x, x⟫_ℂ at hx
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub] at hx
  rw [← hp, ← hm] at hx
  linarith
