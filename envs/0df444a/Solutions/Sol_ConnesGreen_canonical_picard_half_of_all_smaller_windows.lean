-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_of_all_smaller_windows
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:34:06.555491+00:00
-- url     : https://prove2.me/submissions/708c9502-e1eb-47f9-a92c-5c0a8a054d24

import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_ConnesGreen_supported_test_fits_smaller_window
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
theorem solution (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros)
    (hsmall : ∀ t : ℝ, ∀ ht : 0 < t, t < T →
      (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S := by
  apply (canonical_picard_half_iff_original_selected_tests T hT S).mpr
  intro g hg
  obtain ⟨t, ht, htT, hgt⟩ := supported_test_fits_smaller_window T hT g hg
  have hn := (canonical_picard_half_iff_original_selected_tests t ht S).mp
    (hsmall t ht htT) g hgt
  obtain ⟨hp, hm⟩ := canonical_actor_test_norms_window_independent t T ht hT S g hgt hg
  rw [hp, hm]
  exact hn

