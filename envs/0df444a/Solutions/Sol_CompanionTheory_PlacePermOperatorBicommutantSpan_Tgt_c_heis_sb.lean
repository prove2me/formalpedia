-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_heis_sb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:28.958405+00:00
-- url     : https://prove2.me/submissions/eac09299-9332-41a7-8a41-54c354267ae3

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_heis
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_opD
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_sb_opU


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → (∀ x y φ, SB φ → SB (Heisenberg₂ ψ h B x y φ)) ∧ (∀ b φ, SB φ → SB (opU ψ h B b φ)) ∧ ∀ (m : ℝ) (a : Rˣ) (φ : (ι → R) → ℂ), SB φ → SB (opD m (a : R) φ) :=
  fun _ _ _ _ _ _ _ _ _ _ H => ⟨fun x y _ hφ => sb_heis H x y hφ, fun b _ hφ => sb_opU H b hφ, fun m a _ hφ => sb_opD H m a hφ⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
