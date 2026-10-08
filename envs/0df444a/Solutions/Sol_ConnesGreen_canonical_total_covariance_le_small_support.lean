-- Prove2me | solution 1 for ConnesGreen.canonical_total_covariance_le_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T04:57:26.486989+00:00
-- url     : https://prove2.me/submissions/1aae6d82-17c7-4419-ad94-18566f7e41e0

import Theorems.Thm_ConnesGreen_weil_positive_small_support
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem solution (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) :
    canonicalNegativeSynthesis T hT ∘L (canonicalNegativeSynthesis T hT).adjoint ≤
      canonicalPositiveCovariance T hT  := by
  apply (covariance_le_iff_original_tests T hT _
    (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis T hT)).isSelfAdjoint _).mpr
  intro g hg
  have hw := weil_positive_small_support T hT.le hTr g hg
  have hf := canonical_signed_actor_arithmetic T hT g hg
  have hp := (canonicalPositiveSynthesis T hT).adjoint.apply_norm_sq_eq_inner_adjoint_left (sourceEmbed T (problemOneL g))
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  change _ ≤ RCLike.re ⟪(canonicalPositiveSynthesis T hT ∘L (canonicalPositiveSynthesis T hT).adjoint) (sourceEmbed T (problemOneL g)), sourceEmbed T (problemOneL g)⟫_ℂ
  rw [← hp]
  have hL : 0 ≤ ∫ s : ℝ, ‖g s‖ ^ 2 := integral_nonneg (fun s => sq_nonneg _)
  linarith

