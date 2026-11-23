-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.impl_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:19.474941+00:00
-- url     : https://prove2.me/submissions/0c6fd566-1dbc-46c6-9e03-0b7a7ed25712

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : Impl ψ h B μ 1 id :=
  ⟨fun _ hφ => hφ, fun φ hφ => ⟨φ, hφ, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun x y φ _ => by simp⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan
