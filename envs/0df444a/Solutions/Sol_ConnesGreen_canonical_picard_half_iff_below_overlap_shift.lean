-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_below_overlap_shift
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T03:48:54.194975+00:00
-- url     : https://prove2.me/submissions/e9a82b6d-852a-4687-b38d-6f491bc73df3

import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_unrestricted_finite_certificates
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_above_overlap_shift
import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
theorem solution
    (R T : ℝ) (hT : 0 < T) (hTR : T ≤ R) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔
    ∀ δ : ℝ, 0 < δ → δ ≤ arithmeticOverlapShift R →
      ∃ F : Finset CriticalZeros, 0 ≤ canonicalFiniteSelectedCorrection T hT S F δ := by
  rw [canonical_picard_half_iff_unrestricted_finite_certificates]
  constructor
  · intro h δ hδ hle
    exact h δ hδ
  · intro h δ hδ
    by_cases hle : δ ≤ arithmeticOverlapShift R
    · exact h δ hδ hle
    · obtain ⟨F, _, _, _, hF⟩ := canonical_finite_certificate_above_overlap_shift
        R T hT hTR S δ δ (lt_of_not_ge hle) hδ
      exact ⟨F, hF⟩
