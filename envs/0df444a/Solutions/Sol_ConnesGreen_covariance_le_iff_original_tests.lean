-- Prove2me | solution 1 for ConnesGreen.covariance_le_iff_original_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:19:21.279695+00:00
-- url     : https://prove2.me/submissions/b9323339-8c4e-4ab7-92e7-266bba5195b6

import Theorems.Thm_ConnesGreen_testVectorFamily_dense
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
private theorem covariance_le_iff_quadratic {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (N : K →L[ℂ] H) :
    N ∘L N.adjoint ≤ A ↔ ∀ x : H, ‖N.adjoint x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
  have hs := hA.sub (ContinuousLinearMap.isPositive_self_comp_adjoint N).isSelfAdjoint
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_def']
  simp only [hs, true_and]
  apply forall_congr'
  intro x
  have he := N.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  change (0 ≤ RCLike.re ⟪(A - N ∘L N.adjoint) x, x⟫_ℂ) ↔ _
  simp only [sub_apply, inner_sub_left, map_sub]
  rw [← he]
  exact sub_nonneg

theorem solution (t : ℝ) (ht : 0 < t)
    (A : Physical t →L[ℂ] Physical t) (hA : IsSelfAdjoint A)
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : K →L[ℂ] Physical t) :
    N ∘L N.adjoint ≤ A ↔ ∀ g : ℝ → ℂ, SupportedTest t g →
      ‖N.adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
        RCLike.re ⟪A (sourceEmbed t (problemOneL g)), sourceEmbed t (problemOneL g)⟫_ℂ := by
  rw [covariance_le_iff_quadratic A hA N]
  constructor
  · intro h g hg
    exact h _
  · intro h x
    refine (testVectorFamily_dense t ht).induction_on (p := fun x => ‖N.adjoint x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ) x ?_ ?_
    · exact isClosed_le (N.adjoint.continuous.norm.pow 2)
        (Complex.continuous_re.comp (A.continuous.inner (𝕜 := ℂ) continuous_id))
    · intro g
      exact h g.1 g.2

