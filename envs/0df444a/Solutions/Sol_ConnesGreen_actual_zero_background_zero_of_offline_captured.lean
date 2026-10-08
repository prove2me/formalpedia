-- Prove2me | solution 1 for ConnesGreen.actual_zero_background_zero_of_offline_captured
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T17:47:20.873133+00:00
-- url     : https://prove2.me/submissions/8357a5f5-cfe0-44dd-b0a3-05c8291f3a8a

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
theorem solution
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros)
    (hF : ∀ ρ : CriticalZeros, ρ.1.re ≠ 1 / 2 → ρ ∈ F) :
    ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧ B = 0  := by
  refine ⟨0, ?_, rfl⟩
  intro ρ
  have hline : ρ.1.1.re = 1 / 2 := by
    by_contra hn
    exact ρ.2 (hF ρ.1 hn)
  have href : reflectedZero ρ.1 = ρ.1 := by
    apply Subtype.ext
    apply Complex.ext
    · simp [mirror]
      linarith
    · simp [mirror]
  simp [negativeGreenColumn, href]
