-- Prove2me | solution 1 for ConnesGreen.canonical_neutral_shell_zero_of_larger_half
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T07:05:56.875033+00:00
-- url     : https://prove2.me/submissions/d592991d-20c3-4e95-bcae-0d2ee03122d8

import Theorems.Thm_ConnesGreen_canonical_neutral_kernel_persists_of_larger_half
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem solution (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S)
    (x : Physical t) (hx : (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0) :
    (1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint)
      ((canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
        (canonicalSelectedSynthesis T hT S).adjoint) (U x)) = 0 := by
  have hz := (canonical_neutral_kernel_persists_of_larger_half t T ht hT htT S U hU hhalf x).mp hx
  simp [hz]
