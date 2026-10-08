-- Prove2me | solution 1 for ConnesGreen.exists_original_window_actor_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:25:41.293309+00:00
-- url     : https://prove2.me/submissions/24839408-fa6f-48a6-9b7d-7cff9d1f571d

import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace ConnesGreen
private theorem window_inclusion_positive_synthesis (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) :
    U.toContinuousLinearMap.adjoint ∘L canonicalPositiveSynthesis T hT =
      canonicalPositiveSynthesis t ht := by
  apply canonicalPositiveSynthesis_unique t ht
  intro ρ
  simp only [ContinuousLinearMap.comp_apply, canonicalPositiveSynthesis_single]
  simp [positiveGreenColumn, weightedGreenColumn,
    ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU] <;> rfl

private theorem window_inclusion_selected_synthesis (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) :
    U.toContinuousLinearMap.adjoint ∘L canonicalSelectedSynthesis T hT S =
      canonicalSelectedSynthesis t ht S := by
  apply canonicalSelectedSynthesis_unique t ht S
  intro ρ
  simp only [ContinuousLinearMap.comp_apply, canonicalSelectedSynthesis_single]
  simp [negativeGreenColumn, weightedGreenColumn,
    ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU] <;> rfl


end ConnesGreen
/-- Original nested physical carriers and both ORIGINAL actor compressions
are constructed, not assumed. All actual source columns are retained. -/
theorem solution (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      (∀ ρ : CriticalZeros,
        U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
          sourceEmbed t (actualGreenSource ρ)) ∧
      U.toContinuousLinearMap.adjoint ∘L canonicalPositiveSynthesis T hT =
        canonicalPositiveSynthesis t ht ∧
      U.toContinuousLinearMap.adjoint ∘L canonicalSelectedSynthesis T hT S =
        canonicalSelectedSynthesis t ht S := by
  obtain ⟨U, hU⟩ := exists_original_window_inclusion t T ht hT htT
  exact ⟨U, hU, ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU,
    window_inclusion_positive_synthesis t T ht hT htT U hU,
    window_inclusion_selected_synthesis t T ht hT htT S U hU⟩
