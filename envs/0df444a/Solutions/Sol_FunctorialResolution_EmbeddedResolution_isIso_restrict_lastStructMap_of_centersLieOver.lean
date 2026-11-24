-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isIso_restrict_lastStructMap_of_centersLieOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:30.805913+00:00
-- url     : https://prove2.me/submissions/dd8a0bf0-8869-40ab-bdd8-ea82fc2f0409

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_IsoAwayFromCenters
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_restrict
import Theorems.Thm_FunctorialResolution_Blowup_comap_eq_top_of_notMem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_lastStructMap_eq_projectionToBase
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
namespace FunctorialResolution.EmbeddedResolution
private theorem isIso_restrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (h1 : IsIso (f ∣_ (g ⁻¹ᵁ V))) (h2 : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  have := h1
  have := h2
  have h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V) := inferInstance
  rw [morphismRestrict_comp]
  exact h
private theorem isIso_restrict_projectionToBase_of_centersLieOver {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S)
    (i : ℕ) (hi : i ≤ s.length) :
    IsIso (s.projectionToBase i ∣_ U) := by
  revert hi
  induction i with
  | zero =>
    intro _
    show IsIso (s.projectionToBase 0 ∣_ U)
    have h0 : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0).op = 𝟙 (op (0 : ℕ)) := rfl
    have : IsIso (s.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.transitionMap_def, h0, CategoryTheory.Functor.map_id,
        Category.id_comp]
      infer_instance
    infer_instance
  | succ i ih =>
    intro hi
    have hi' : i < s.length := hi
    have h2 : IsIso (s.projectionToBase i ∣_ U) := ih (Nat.le_of_succ_le hi)
    have hcomp : s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) :=
      s.transitionMap_comp_projectionToBase (Nat.le_succ i)
    have hb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi'
    have hres := hb.restrict (s.projectionToBase i ⁻¹ᵁ U)
    have htop : (s.center i).comap (s.projectionToBase i ⁻¹ᵁ U).ι = ⊤ := by
      apply Blowup.comap_eq_top_of_notMem_support
      intro x hx
      have h1 := hs i hi' ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) hx
      have hxV : (s.projectionToBase i ⁻¹ᵁ U).ι.base x
          ∈ ((s.projectionToBase i ⁻¹ᵁ U : (s.schemeAt i).Opens) : Set (s.schemeAt i)) := by
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self x
      have h2' : (s.projectionToBase i).base ((s.projectionToBase i ⁻¹ᵁ U).ι.base x) ∈ (U : Set X) := hxV
      exact Set.disjoint_left.mp hU h2' h1
    rw [htop] at hres
    have h1 : IsIso (s.transitionMapSucc i ∣_ (s.projectionToBase i ⁻¹ᵁ U)) := hres.isIso_of_top
    have key : IsIso ((s.transitionMapSucc i ≫ s.projectionToBase i) ∣_ U) :=
      isIso_restrict_comp (s.transitionMapSucc i) (s.projectionToBase i) U h1 h2
    rw [hcomp] at key
    exact key
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (S : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S) :
    IsIso (s.lastStructMap ∣_ U) := by
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase]
  exact isIso_restrict_projectionToBase_of_centersLieOver s S U hU hs s.length le_rfl
end FunctorialResolution.EmbeddedResolution
