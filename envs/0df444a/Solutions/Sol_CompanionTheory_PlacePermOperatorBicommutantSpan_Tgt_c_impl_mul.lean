-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_impl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:31.315915+00:00
-- url     : https://prove2.me/submissions/c2b25d39-4e0b-4859-9785-e87ca9de7b85

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_impl_mul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_impl_one


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → Impl ψ h B μ 1 id ∧ ∀ (g g' : SL(2, R)) T T', Impl ψ h B μ g T → Impl ψ h B μ g' T' → Impl ψ h B μ (g * g') (T ∘ T') :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ⟨impl_one, fun _ _ _ _ h1 h2 => impl_mul h1 h2⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
