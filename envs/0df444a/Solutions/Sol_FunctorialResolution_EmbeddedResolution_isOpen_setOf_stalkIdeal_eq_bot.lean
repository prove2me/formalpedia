-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isOpen_setOf_stalkIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:11.668256+00:00
-- url     : https://prove2.me/submissions/26b0f2b9-06e9-43d0-a46e-8b08fbbf6854

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_LocallyBoundedOrder
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_stalkIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal



set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (J : X.IdealSheafData) :
    IsOpen {x : ↥X | stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x)) := hx
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    have h1 : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  obtain ⟨s, hs⟩ : (J.ideal U).FG := IsNoetherian.noetherian (J.ideal U)
  have hzero : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) x hxU).hom g = 0 := by
    intro g hg
    have hgI : g ∈ J.ideal U := by
      rw [← hs]
      exact Submodule.subset_span (Finset.mem_coe.mpr hg)
    have hmem := germ_mem_stalkIdeal J x U hxU hgI
    rw [hx'] at hmem
    simpa using hmem
  have hWex : ∀ g : Γ(X, (U : X.Opens)), ∃ (W : X.Opens) (i : W ⟶ (U : X.Opens)),
      x ∈ W ∧ (g ∈ s → (X.presheaf.map i.op).hom g = 0) := by
    intro g
    by_cases hg : g ∈ s
    · obtain ⟨V, iV, hxV, hi⟩ :=
        X.toLocallyRingedSpace.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero
          (U : X.Opens) g ⟨x, hxU⟩ (hzero g hg)
      exact ⟨V, iV, hxV, fun _ => hi⟩
    · exact ⟨(U : X.Opens), 𝟙 _, hxU, fun h => absurd h hg⟩
  choose W i hxW hres using hWex
  refine ⟨((U : X.Opens) : Set ↥X) ∩
      ⋂ g ∈ (s : Set Γ(X, (U : X.Opens))), ((W g : X.Opens) : Set ↥X), ?_, ?_, ?_⟩
  · rintro y ⟨hyU, hyW⟩
    have hyW' : ∀ g ∈ s, y ∈ W g := fun g hg =>
      Set.mem_iInter₂.mp hyW g (Finset.mem_coe.mpr hg)
    have hmain : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) y hyU).hom g = 0 := by
      intro g hg
      have h3 : (X.presheaf.germ (W g) y (hyW' g hg)).hom
          ((X.presheaf.map (i g).op).hom g) = 0 := by
        rw [hres g hg, map_zero]
      exact (X.presheaf.germ_res_apply (i g) y (hyW' g hg) g).symm.trans h3
    show stalkIdeal J y = ⊥
    rw [stalkIdeal_eq_map_germ J y U hyU, ← le_bot_iff, Ideal.map_le_iff_le_comap, ← hs,
      Submodule.span_le]
    intro g hg
    have hg0 := hmain g (Finset.mem_coe.mp hg)
    have hmem : (X.presheaf.germ (U : X.Opens) y hyU).hom g ∈
        (⊥ : Ideal (X.presheaf.stalk y)) := by
      rw [hg0]
      exact Submodule.zero_mem _
    simpa using hmem
  · exact (TopologicalSpace.Opens.isOpen (U : X.Opens)).inter
      (Set.Finite.isOpen_biInter s.finite_toSet
        (fun g _ => TopologicalSpace.Opens.isOpen (W g)))
  · exact ⟨hxU, Set.mem_iInter₂.mpr (fun g _ => hxW g)⟩
end FunctorialResolution.EmbeddedResolution
