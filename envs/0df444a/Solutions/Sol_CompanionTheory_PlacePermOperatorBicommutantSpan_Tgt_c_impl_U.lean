-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_impl_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:14:45.5007+00:00
-- url     : https://prove2.me/submissions/e46b673a-660f-4068-9b43-ceab974d42ca

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_impl_U


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ b : R, Impl ψ h B μ (nMat b) (opU ψ h B b) :=
  fun _ _ _ _ _ _ _ _ _ _ H b => impl_U H b
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
