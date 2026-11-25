-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_sb_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:53.954881+00:00
-- url     : https://prove2.me/submissions/e4063903-604f-4824-a179-01d2df059973

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_span


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V, IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) → ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x :=
  fun _ _ _ _ _ _ h φ hφ L hL hinv => by
    have := h.1
    obtain ⟨s, hs⟩ := sb_span hφ hL hinv
    exact ⟨s, fun x => (congrFun hs x).trans (Finset.sum_apply _ _ _)⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
