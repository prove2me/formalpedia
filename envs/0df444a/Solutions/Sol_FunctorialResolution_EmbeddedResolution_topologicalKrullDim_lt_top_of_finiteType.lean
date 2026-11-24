-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_top_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:32.344658+00:00
-- url     : https://prove2.me/submissions/3173c38b-513c-4a24-ba9d-6dca9a4d4bb1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_lt_top_of_finite_isOpenCover
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_spec_lt_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_eq_of_homeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups


section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem topologicalKrullDim_lt_top_of_homeomorph {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (h : topologicalKrullDim B < ⊤) :
    topologicalKrullDim A < ⊤ := by
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h
private theorem topologicalKrullDim_affineOpen_lt_top {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f) {U : X.Opens}
    (hU : IsAffineOpen U) : topologicalKrullDim ↥((U : Set ↥X)) < ⊤ := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := le_top
  have hQ : RingHom.FiniteType ((f.appLE ⊤ U hle).hom) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f hft
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of k))⟩ ⟨U, hU⟩ hle
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom := by
    intro y
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom y, ?_⟩
    have hid := (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) y) hid
  let _ : Algebra k Γ(X, U) :=
    RingHom.toAlgebra (((f.appLE ⊤ U hle).hom).comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom)
  have : Algebra.FiniteType k Γ(X, U) :=
    hQ.comp (RingHom.FiniteType.of_surjective _ hsurj)
  have e : ↥((U : Set ↥X)) ≃ₜ ↥(Spec Γ(X, U)) := Scheme.homeoOfIso hU.isoSpec
  exact topologicalKrullDim_lt_top_of_homeomorph e (topologicalKrullDim_spec_lt_top k Γ(X, U))
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f) :
    topologicalKrullDim ↥X < ⊤ := by
  classical
  have hcompact : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    simp
  have : CompactSpace ↥X := by
    constructor
    have h := hqc.isCompact_preimage Set.univ isOpen_univ hcompact
    simpa using h
  have hcov : ⋃ i : X.affineOpens, ((i : X.Opens) : Set ↥X) = Set.univ := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top X, Opens.coe_top]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => ((i : X.Opens) : Set ↥X))
    (fun i => ((i : X.Opens)).isOpen) hcov.ge
  refine topologicalKrullDim_lt_top_of_finite_isOpenCover
    (ι := {i : X.affineOpens // i ∈ t})
    (fun i => ((i.1 : X.Opens) : Set ↥X)) (fun i => ((i.1 : X.Opens)).isOpen) ?_ ?_
  · refine Set.eq_univ_of_univ_subset ?_
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  · intro i
    exact topologicalKrullDim_affineOpen_lt_top f hft i.1.2
end FunctorialResolution.EmbeddedResolution
