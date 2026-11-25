-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_fou_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:20:10.69342+00:00
-- url     : https://prove2.me/submissions/97c9c0cf-ee64-4062-bafd-2a280784a984

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_ind
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_ind_of_not


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
open CompanionTheory.PlacePermOperatorBicommutantSpan
namespace CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V, fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y = ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y :=
  fun _ _ _ _ χ _ h L h1 h2 a y => by
    have := fou_ind h ⟨h1, h2⟩ a y
    have e : ind 0 (perpG h L) y = Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
      by_cases hy : y ∈ perp χ (L : Set _)
      · rw [ind_of_mem (by rw [sub_zero]; exact hy), Set.indicator_of_mem hy]
      · rw [ind_of_not (by rw [sub_zero]; exact hy), Set.indicator_of_notMem hy]
    rwa [e] at this
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
