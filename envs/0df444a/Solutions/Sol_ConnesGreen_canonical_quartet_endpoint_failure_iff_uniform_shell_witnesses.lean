-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_endpoint_failure_iff_uniform_shell_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T06:36:10.458983+00:00
-- url     : https://prove2.me/submissions/9f1b6c0c-86e5-45f9-9b21-c7fe03ae8c24

import Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_half_iff_original_shell_obligations
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T →
            (∃ U : Physical c →ₗᵢ[ℂ] Physical T,
              ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
                U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
            ∀ U : Physical c →ₗᵢ[ℂ] Physical T,
              (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
                U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) →
              let D := ((1 / 2 - η)⁻¹ - 1) • canonicalPositiveCovariance T hT -
                canonicalSelectedSynthesis T hT (quartet ρ) ∘L
                  (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
              (∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
                RCLike.re ⟪D z, z⟫_ℂ < 0) ∨
              (∃ x : Physical c, ∃ z : Physical T,
                U.toContinuousLinearMap.adjoint z = 0 ∧
                RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ <
                  ‖⟪D (U x), z⟫_ℂ‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ :=
    canonical_quartet_endpoint_half_iff_original_shell_obligations ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  constructor
  · intro hno
    have hn := (not_congr he).mp hno
    push_neg at hn
    obtain ⟨η, hη, hηhalf, hn⟩ := hn
    refine ⟨η, hη, hηhalf, ?_⟩
    intro T hT hcT
    refine ⟨exists_original_window_inclusion c T hc hT hcT.le, ?_⟩
    intro U hU
    have hbad := hn T hT hcT U hU
    dsimp only at hbad ⊢
    push_neg +distrib at hbad
    exact hbad
  · rintro ⟨η, hη, hηhalf, hb⟩ ha
    obtain ⟨T, hT, hcT, U, hU, hs⟩ := (he.mp ha) η hη hηhalf
    have hn := (hb T hT hcT).2 U hU
    dsimp only at hs hn
    rcases hn with ⟨z, hz, hneg⟩ | ⟨x, z, hz, hbad⟩
    · exact (not_lt_of_ge (hs.1 z hz)) hneg
    · exact (not_lt_of_ge (hs.2 x z hz)) hbad
