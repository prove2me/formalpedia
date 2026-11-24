-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_eq_of_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:55.714598+00:00
-- url     : https://prove2.me/submissions/3ad92b32-88c6-4879-bacf-d79550dc0059

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
open Order in
private theorem topologicalKrullDim_eq_iSup_length {Z : Type*} [TopologicalSpace Z] :
    topologicalKrullDim Z =
      ⨆ p : LTSeries (IrreducibleCloseds Z), (p.length : WithBot ℕ∞) := rfl
private theorem coe_irreducibleClosedsMapOfHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : IrreducibleCloseds X) :
    ((irreducibleClosedsMapHomeomorph e a : IrreducibleCloseds Y) : Set Y) = e '' (a : Set X) := rfl
private theorem strictMono_irreducibleClosedsMapOfHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : StrictMono (irreducibleClosedsMapHomeomorph e) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, coe_irreducibleClosedsMapOfHomeomorph, coe_irreducibleClosedsMapOfHomeomorph]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)
  · intro h
    have h1 : e '' (a : Set X) = e '' (b : Set X) := by
      rw [← coe_irreducibleClosedsMapOfHomeomorph e a, ← coe_irreducibleClosedsMapOfHomeomorph e b, h]
    exact hab.ne (SetLike.coe_injective (Set.image_injective.mpr e.injective h1))
open Order in
private theorem topologicalKrullDim_le_of_homeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_length (Z := X), topologicalKrullDim_eq_iSup_length (Z := Y)]
  refine iSup_le fun p => ?_
  have h := le_iSup (fun r : LTSeries (IrreducibleCloseds Y) => (r.length : WithBot ℕ∞))
    (p.map (irreducibleClosedsMapHomeomorph e) (strictMono_irreducibleClosedsMapOfHomeomorph e))
  exact h
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_homeomorph e) (topologicalKrullDim_le_of_homeomorph e.symm)
end FunctorialResolution.EmbeddedResolution
