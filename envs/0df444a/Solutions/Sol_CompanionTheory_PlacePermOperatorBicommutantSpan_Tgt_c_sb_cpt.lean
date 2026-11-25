-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_sb_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:44.02481+00:00
-- url     : https://prove2.me/submissions/1b909e33-3f2a-44af-acd8-6de4ffb69f81

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_co_cpt
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_level


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x :=
  fun _ _ _ _ _ _ h => ⟨fun _ hK => (co_cpt h hK).imp fun _ hL => ⟨hL.1.1, hL.1.2, hL.2⟩, fun _ hφ => by
    obtain ⟨L, L', h1, h2, h3, h4, h5⟩ := sb_level h hφ
    exact ⟨L, L', h1.1, h1.2, h2.1, h2.2, h3, h4, h5⟩⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
