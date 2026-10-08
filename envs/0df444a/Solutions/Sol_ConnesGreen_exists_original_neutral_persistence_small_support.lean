-- Prove2me | solution 1 for ConnesGreen.exists_original_neutral_persistence_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:35:27.674636+00:00
-- url     : https://prove2.me/submissions/b8c705d9-5d49-400e-adbe-738cc3b6fc8b

import Theorems.Thm_ConnesGreen_canonical_selected_covariance_le_small_support
import Theorems.Thm_ConnesGreen_RG0Integration_exists_original_neutral_window_inclusion
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (hTr : T ≤ positiveSupportRadius)
    (S : Finset CriticalZeros) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      ∀ x : Physical t,
        (canonicalPositiveCovariance t ht -
          canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
        (canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by
  exact ConnesGreen.RG0Integration.exists_original_neutral_window_inclusion t T ht hT htT S
    (sub_nonneg.mpr (ConnesGreen.canonical_selected_covariance_le_small_support T hT hTr S))
