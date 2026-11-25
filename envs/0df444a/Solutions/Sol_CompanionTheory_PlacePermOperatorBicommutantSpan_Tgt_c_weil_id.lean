-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_weil_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:29:35.084824+00:00
-- url     : https://prove2.me/submissions/75817e0f-53f3-437b-8e92-1c4c181ece44

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_weil_id


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ (b : Rˣ) (m : ℝ), 0 < m → (∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) → ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) = γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R) (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) :=
  fun _ _ _ _ _ _ _ _ _ _ H b _ hm hμ => weil_id H b hm hμ
end CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt
