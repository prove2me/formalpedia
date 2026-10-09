-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_unshifted_shell_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T18:36:56.094493+00:00
-- url     : https://prove2.me/submissions/53130a00-95b4-4f63-b6c0-153a91298319

import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_half_iff_covariance
import Theorems.Thm_WeilDefect_MarkerStability_nonnegative_iff_shell_and_cross_budget
import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_RG0Integration_signed_covariance_compression
import Theorems.Thm_ConnesGreen_positiveSupportRadius_positive
import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_small_support_constants
open Complex ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem fixed_shell_helper
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T)
    (S : Finset CriticalZeros) (U : Physical c →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
      U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S) :
    let D := canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔
    (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
      0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
    (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
      ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ) := by
  dsimp only
  rw [RG0Integration.original_picard_half_iff_covariance, ← sub_nonneg]
  let A := canonicalPositiveCovariance T hT -
    canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
  let C := canonicalPositiveCovariance c hc -
    canonicalSelectedSynthesis c hc S ∘L (canonicalSelectedSynthesis c hc S).adjoint
  have hA : IsSelfAdjoint A :=
    (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis T hT)).isSelfAdjoint.sub
      (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalSelectedSynthesis T hT S)).isSelfAdjoint
  have hC : 0 ≤ C := sub_nonneg.mpr
    ((RG0Integration.original_picard_half_iff_covariance c hc S).mp hhalf)
  have hcomp : U.toContinuousLinearMap.adjoint ∘L A ∘L U.toContinuousLinearMap = C :=
    RG0Integration.signed_covariance_compression c T hc hT S U
      (RG0Integration.window_inclusion_original_source_adjoint c T hc hT hcT U hU)
  have hcore : ∀ x : Physical c, 0 ≤ RCLike.re ⟪A (U x), U x⟫_ℂ := by
    intro x
    have he : U.toContinuousLinearMap.adjoint (A (U x)) = C x := by
      simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap] using congrArg (fun B => B x) hcomp
    have hi := U.toContinuousLinearMap.adjoint_inner_left x (A (U x))
    simp only [LinearIsometry.coe_toContinuousLinearMap] at hi
    rw [he] at hi
    rw [← hi]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := C)).mp hC).re_inner_nonneg_left x
  exact nonnegative_iff_shell_and_cross_budget A hA U hcore

theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → ∀ U : Physical c →ₗᵢ[ℂ] Physical T,
        (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
          U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) →
        let D := canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT (quartet ρ) ∘L
            (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
        (∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
          RCLike.re ⟪D z, z⟫_ℂ < 0) ∨
        (∃ x : Physical c, ∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
          RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ < ‖⟪D (U x), z⟫_ℂ‖ ^ 2) := by
  obtain ⟨c, hrc, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
  have hc : 0 < c := positiveSupportRadius_positive.trans_le hrc
  refine ⟨c, hc, hrc, ?_⟩
  intro T hT hcT U hU
  have hbad := (hcut T hT).not.mpr (not_le_of_gt hcT)
  have hbad' := (fixed_shell_helper c T hc hT hcT.le
    (quartet ρ) U hU ((hcut c hc).mpr le_rfl)).not.mp hbad
  simpa only [not_and_or, not_forall, Classical.not_imp, not_le, exists_prop] using hbad'
