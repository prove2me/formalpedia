-- Prove2me | solution 1 for ConnesGreen.canonical_half_cut_unique
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:52:20.777772+00:00
-- url     : https://prove2.me/submissions/de9e7d5b-bd28-45af-8649-fcc2433f54bc

import Theorems.Thm_ConnesGreen_positiveSupportRadius_positive
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (S : Finset CriticalZeros)
    (c d : ℝ) (hc : positiveSupportRadius ≤ c) (hd : positiveSupportRadius ≤ d)
    (hcutc : (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ c))
    (hcutd : (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ d)) : c = d := by
  have hcpos : 0 < c := positiveSupportRadius_positive.trans_le hc
  have hdpos : 0 < d := positiveSupportRadius_positive.trans_le hd
  exact le_antisymm ((hcutd c hcpos).mp ((hcutc c hcpos).mpr le_rfl))
    ((hcutc d hdpos).mp ((hcutd d hdpos).mpr le_rfl))
