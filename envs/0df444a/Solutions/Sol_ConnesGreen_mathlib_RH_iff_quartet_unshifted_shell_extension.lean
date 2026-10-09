-- Prove2me | solution 1 for ConnesGreen.mathlib_RH_iff_quartet_unshifted_shell_extension
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T18:35:51.697029+00:00
-- url     : https://prove2.me/submissions/7c5c8186-d0b7-4fe1-bf06-fbf941b4bd84

import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_half_iff_covariance
import Theorems.Thm_WeilDefect_MarkerStability_nonnegative_iff_shell_and_cross_budget
import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_RG0Integration_signed_covariance_compression
import Theorems.Thm_ConnesGreen_positiveSupportRadius_positive
import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Theorems.Thm_ConnesGreen_mathlib_RH_iff_cofinal_quartet_half_windows
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
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

private theorem extension_shell_helper
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S) :
    (∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
      (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔
    ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧ ∃ U : Physical c →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
        U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      let D := canonicalPositiveCovariance T hT -
        canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
      (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
        0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
      (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
        ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ) := by
  constructor
  · rintro ⟨T, hT, hcT, hb⟩
    obtain ⟨U, hU⟩ := exists_original_window_inclusion c T hc hT hcT.le
    exact ⟨T, hT, hcT, U, hU,
      (fixed_shell_helper c T hc hT hcT.le S U hU hhalf).mp hb⟩
  · rintro ⟨T, hT, hcT, U, hU, hb⟩
    exact ⟨T, hT, hcT,
      (fixed_shell_helper c T hc hT hcT.le S U hU hhalf).mpr hb⟩

private theorem rh_extension_helper :
    RiemannHypothesis ↔ ∀ ρ : CriticalZeros, ∀ c : ℝ, ∀ hc : 0 < c,
      ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker c hc (quartet ρ)) →
      ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
        (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) := by
  constructor
  · intro h ρ c hc _
    exact mathlib_RH_iff_cofinal_quartet_half_windows.mp h ρ c
  · intro h
    apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
    intro s hz hlo hhi
    by_contra hoff
    let ρ : CriticalZeros := ⟨s, hz, hlo, hhi⟩
    obtain ⟨c, hrc, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
    have hc : 0 < c := positiveSupportRadius_positive.trans_le hrc
    obtain ⟨T, hT, hcT, hb⟩ := h ρ c hc ((hcut c hc).mpr le_rfl)
    exact (not_le_of_gt hcT) ((hcut T hT).mp hb)

theorem solution :
    RiemannHypothesis ↔ ∀ ρ : CriticalZeros, ∀ c : ℝ, ∀ hc : 0 < c,
      ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker c hc (quartet ρ)) →
      ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧ ∃ U : Physical c →ₗᵢ[ℂ] Physical T,
        (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
          U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
        let D := canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT (quartet ρ) ∘L
            (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
        (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
        (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ) := by
  rw [rh_extension_helper]
  apply forall_congr'
  intro ρ
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  apply imp_congr_right
  intro hhalf
  exact extension_shell_helper c hc (quartet ρ) hhalf
