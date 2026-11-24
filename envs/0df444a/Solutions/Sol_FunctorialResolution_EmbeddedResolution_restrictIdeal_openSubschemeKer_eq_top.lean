-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_openSubschemeKer_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:54.159273+00:00
-- url     : https://prove2.me/submissions/466899d0-871f-4e40-99ae-1063f47b6478

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_openSubschemeKer
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complOpensOfIsClosed
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem comap_eq_ker_fst {A B : Scheme.{u}} (f : A ⟶ B) (I : B.IdealSheafData) :
    I.comap f = (Limits.pullback.fst f I.subschemeι).ker := rfl
private theorem comap_opensι_eq_ker_morphismRestrict {T : Scheme.{u}} (K : T.IdealSheafData)
    (V : T.Opens) : K.comap (Scheme.Opens.ι V) = (K.subschemeι ∣_ V).ker := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  rw [comap_eq_ker_fst, ← hfac, Scheme.Hom.ker_comp_of_isIso]
private theorem subsingleton_sections_of_eq_bot {Y : Scheme.{u}} (V : Y.Opens)
    (hV : V = ⊥) : Subsingleton ↥(Y.presheaf.obj (Opposite.op V)) := by
  have h : CategoryTheory.Limits.IsTerminal (Y.presheaf.obj (Opposite.op V)) :=
    Y.sheaf.isTerminalOfEqEmpty hV
  exact CommRingCat.subsingleton_of_isTerminal h
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (U : X.Opens)
    (hU : ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U) :
    restrictIdeal (openSubschemeKer Z W) U = ⊤ := by
  have hnot : ∀ y : (openSubschemeKer Z W).subscheme,
      (openSubschemeKer Z W).subschemeι.base y ∉ U := by
    intro y hy
    have hmem : (openSubschemeKer Z W).subschemeι.base y ∈ ((openSubschemeKer Z W).support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self y
    rw [support_openSubschemeKer Z W hW] at hmem
    obtain ⟨w, hwW, hw⟩ := hmem
    refine hU w hwW ?_
    rw [hw]
    exact hy
  have hempty : ∀ _y : ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U).toScheme, False := by
    intro y
    have h1 : (Scheme.Opens.ι ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U)).base y ∈
        ((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U : Set (openSubschemeKer Z W).subscheme) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self y
    exact hnot _ h1
  have hObot : ∀ O : (((openSubschemeKer Z W).subschemeι ⁻¹ᵁ U).toScheme).Opens, O = ⊥ := by
    intro O
    refine le_antisymm ?_ bot_le
    intro y _
    exact (hempty y).elim
  have hqcm : QuasiCompact ((openSubschemeKer Z W).subschemeι ∣_ U) := by
    refine ⟨fun O _ _ => ?_⟩
    have hE : (⇑((openSubschemeKer Z W).subschemeι ∣_ U).base ⁻¹' O) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro _
      exact hempty y
    rw [hE]
    exact isCompact_empty
  rw [restrictIdeal_eq_comap_ι, comap_opensι_eq_ker_morphismRestrict (openSubschemeKer Z W) U]
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hker : RingHom.ker (CommRingCat.Hom.hom
      (((openSubschemeKer Z W).subschemeι ∣_ U).app V.1)) = ⊤ := by
    have := subsingleton_sections_of_eq_bot
      (((openSubschemeKer Z W).subschemeι ∣_ U) ⁻¹ᵁ V.1) (hObot _)
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply ((openSubschemeKer Z W).subschemeι ∣_ U) V, hker]
  simp
end FunctorialResolution.EmbeddedResolution
