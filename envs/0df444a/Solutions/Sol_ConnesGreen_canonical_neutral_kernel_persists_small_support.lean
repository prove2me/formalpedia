-- Prove2me | solution 1 for ConnesGreen.canonical_neutral_kernel_persists_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:35:26.500145+00:00
-- url     : https://prove2.me/submissions/d5b9992f-7bcf-437f-8617-2587be42eff4

import Theorems.Thm_ConnesGreen_canonical_selected_covariance_le_small_support
import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_RG0Integration_original_neutral_kernel_persists_of_source_compression
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (hTr : T ≤ positiveSupportRadius)
    (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) (x : Physical t) :
    (canonicalPositiveCovariance t ht -
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
    (canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by
  exact ConnesGreen.RG0Integration.original_neutral_kernel_persists_of_source_compression
    t T ht hT S U
    (fun ρ => ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU ρ)
    (sub_nonneg.mpr (ConnesGreen.canonical_selected_covariance_le_small_support T hT hTr S)) x
