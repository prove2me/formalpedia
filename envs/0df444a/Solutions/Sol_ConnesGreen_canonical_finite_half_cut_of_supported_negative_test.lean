-- Prove2me | solution 1 for ConnesGreen.canonical_finite_half_cut_of_supported_negative_test
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T06:03:53.956266+00:00
-- url     : https://prove2.me/submissions/2eab038a-b6df-418e-91ab-ef3076e210fd

import Theorems.Thm_ConnesGreen_canonical_half_window_dichotomy
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open WeilDefect.MarkerStability
theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0):
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧ c < t ∧
      ∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S ↔ T ≤ c) := by
  classical
  have hbad : ¬ (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S := by
    intro hh
    have hpos := (canonical_picard_half_iff_original_selected_tests t ht S).mp hh g hg
    exact (not_le_of_gt hn) hpos
  rcases canonical_half_window_dichotomy S with hall | hcut
  · exact False.elim (hbad (hall t ht))
  · obtain ⟨c, hrc, hcut⟩ := hcut
    have hct : c < t := by
      by_contra h
      exact hbad ((hcut t ht).mpr (le_of_not_gt h))
    exact ⟨c, hrc, hct, hcut⟩
