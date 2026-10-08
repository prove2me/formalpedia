-- Prove2me | solution 1 for ConnesGreen.RG0Integration.original_neutral_kernel_persists_of_source_compression
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:48:29.180663+00:00
-- url     : https://prove2.me/submissions/1666dcb1-91ac-481b-9227-0e299567cfd5

import Theorems.Thm_ConnesGreen_RG0Integration_signed_covariance_compression
import Theorems.Thm_WeilDefect_MarkerStability_nonnegative_compression_kernel_iff
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section


theorem solution (t T : ℝ)
    (ht : 0 < t) (hT : 0 < T) (S : Finset CriticalZeros)
    (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hsource : ∀ ρ : CriticalZeros,
      U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
        sourceEmbed t (actualGreenSource ρ))
    (hpos : 0 ≤ canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) (x : Physical t) :
    (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L
      (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
    (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
      (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by
  rw [← ConnesGreen.RG0Integration.signed_covariance_compression t T ht hT S U hsource]
  exact nonnegative_compression_kernel_iff _ hpos U.toContinuousLinearMap x
