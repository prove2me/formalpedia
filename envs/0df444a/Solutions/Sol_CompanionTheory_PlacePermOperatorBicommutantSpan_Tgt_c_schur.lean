-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:57.944905+00:00
-- url     : https://prove2.me/submissions/3343250b-7eaa-4da9-8fe6-fe13edb43c5d

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_schur


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ T : (V → ℂ) → (V → ℂ), (∀ φ, SB φ → SB (T φ)) → (∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ') → (∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) → (∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u) → (∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) → ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ :=
  fun _ _ _ _ _ _ h _ _ h1 h2 h3 h4 => schur h h1 h2 h3 h4
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
