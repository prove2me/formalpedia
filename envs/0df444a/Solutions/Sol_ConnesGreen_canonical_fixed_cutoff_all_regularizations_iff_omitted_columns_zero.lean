-- Prove2me | solution 1 for ConnesGreen.canonical_fixed_cutoff_all_regularizations_iff_omitted_columns_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:46:19.919957+00:00
-- url     : https://prove2.me/submissions/8ba06fa7-b23d-4218-86b7-6a5d3239d0c3

import Definitions.Def_ConnesGreen_RG0_original_actors
import Theorems.Thm_WeilDefect_MarkerStability_covariance_relative_bound_all_regularizations_iff_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
/-- A single fixed ORIGINAL cutoff satisfying relative tail bounds at ALL
positive regularizations would have zero ORIGINAL background synthesis. -/
private theorem canonical_fixed_cutoff_all_regularizations_iff_background_zero
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖canonicalTailCovariance t ht F‖ ≤ α * ε) ↔
      canonicalBackgroundSynthesis t ht F = 0 := by
  exact covariance_relative_bound_all_regularizations_iff_zero
    (canonicalBackgroundSynthesis t ht F) α hα
end ConnesGreen
/-- Exact original-actor boundary: a fixed cutoff working at EVERY scale
requires ALL omitted original negative columns to vanish, not just be small. -/
theorem solution
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (α : ℝ) (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ‖canonicalTailCovariance t ht F‖ ≤ α * ε) ↔
      ∀ ρ : {ρ : CriticalZeros // ρ ∉ F},
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1 = 0 := by
  rw [canonical_fixed_cutoff_all_regularizations_iff_background_zero t ht F α hα]
  constructor
  · intro hb ρ
    have hc := canonicalBackgroundSynthesis_single t ht F ρ
    rw [hb] at hc
    exact hc.symm
  · intro hc
    apply (canonicalBackgroundSynthesis_unique t ht F 0 ?_).symm
    intro ρ
    simpa using (hc ρ).symm
