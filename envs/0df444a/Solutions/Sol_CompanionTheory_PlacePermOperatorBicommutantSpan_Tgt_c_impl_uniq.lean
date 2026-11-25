-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_impl_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:16.719989+00:00
-- url     : https://prove2.me/submissions/afdcf675-97f8-4dad-8b74-097521ac82b0

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_impl_uniq


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (g : SL(2, R)) T T', Impl ψ h B μ g T → Impl ψ h B μ g T' → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, SB φ → T' φ = c • T φ :=
  fun _ _ _ _ _ _ _ _ _ _ H _ _ _ h1 h2 => impl_uniq H h1 h2
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
