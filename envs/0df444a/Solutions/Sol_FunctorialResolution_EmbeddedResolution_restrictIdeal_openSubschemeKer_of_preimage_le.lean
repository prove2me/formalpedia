-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_openSubschemeKer_of_preimage_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:08.789466+00:00
-- url     : https://prove2.me/submissions/d54a82b9-d3c3-412d-8dda-ce7447eb3754

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_openSubschemeKer_eq_ker
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_bijective_appLE_of_image_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_appLE_congr_hom
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
private theorem image_preimage_opensι_of_le {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V) :
    Scheme.Opens.ι V ''ᵁ (Scheme.Opens.ι V ⁻¹ᵁ O) = O := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  refine inf_eq_right.mpr ?_
  intro x hx
  show x ∈ Set.range ⇑(Scheme.Opens.ι V).base
  rw [Scheme.Opens.range_ι]
  exact h hx
private theorem injective_app_opensι_of_le {Y : Scheme.{u}} (V O : Y.Opens) (h : O ≤ V) :
    Function.Injective (CommRingCat.Hom.hom ((Scheme.Opens.ι V).app O)) := by
  have hb := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V) O
    (Scheme.Opens.ι V ⁻¹ᵁ O) le_rfl (image_preimage_opensι_of_le V O h)
  rw [Scheme.Hom.app_eq_appLE]
  exact hb.1
private theorem ker_app_morphismRestrict_eq_map_ker {Y T : Scheme.{u}} (m : Y ⟶ T) (V : T.Opens)
    (P : V.toScheme.affineOpens)
    (e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) :
    RingHom.ker (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
      = Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι V)
            (Scheme.Opens.ι V ''ᵁ P.1) P.1 e))
          (RingHom.ker (CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1)))) := by
  have hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι V).preimage_image_eq P.1
  have hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) := by
    rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]
  have hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V := Scheme.Opens.ι_image_le ..
  have hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V := fun x hx => hQV hx
  have himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1)
      = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := by
    rw [hpre2]
    exact image_preimage_opensι_of_le (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle
  have hbij := AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V)
    (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl
  have hinj := (AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq
    (Scheme.Opens.ι (m ⁻¹ᵁ V)) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1))
    ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1
  have hsq : Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e ≫
        (m ∣_ V).app P.1
      = m.app (Scheme.Opens.ι V ''ᵁ P.1) ≫
        Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le := by
    rw [Scheme.Hom.app_eq_appLE (m ∣_ V), Scheme.Hom.app_eq_appLE m,
      Scheme.Hom.appLE_comp_appLE (m ∣_ V) (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1
        ((m ∣_ V) ⁻¹ᵁ P.1) e le_rfl,
      Scheme.Hom.appLE_comp_appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) m (Scheme.Opens.ι V ''ᵁ P.1)
        (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) le_rfl hpre2.le]
    exact AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) _ _ _ _
  have hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
        ((CommRingCat.Hom.hom
          (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le))
        ((CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1))) x) := by
    intro x
    have h' := congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [RingHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker]
    apply hinj
    rw [← hsqr x, hy, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hsqr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
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
    (hU : (Z.subschemeι ⁻¹ᵁ U) ≤ W) :
    restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U := by
  have hindW : Topology.IsInducing ⇑(Scheme.Opens.ι W).base :=
    (Scheme.Opens.ι W).isEmbedding.toIsInducing
  have hrangeW : Set.range ⇑(Scheme.Opens.ι W).base = (W : Set Z.subscheme) := by
    rw [Scheme.Opens.range_ι]
  have hqcW : QuasiCompact (Scheme.Opens.ι W) := by
    refine ⟨fun V _ hVc => ?_⟩
    refine hindW.isCompact_iff.mpr ?_
    rw [Set.image_preimage_eq_inter_range, hrangeW]
    exact hVc.inter_right hW
  have hqc : QuasiCompact (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hqc1 : QuasiCompact ((openSubschemeKer Z W).subschemeι ∣_ U) := inferInstance
  have hqc2 : QuasiCompact (Z.subschemeι ∣_ U) := inferInstance
  rw [restrictIdeal_eq_comap_ι (openSubschemeKer Z W) U, restrictIdeal_eq_comap_ι Z U,
    comap_opensι_eq_ker_morphismRestrict (openSubschemeKer Z W) U,
    comap_opensι_eq_ker_morphismRestrict Z U]
  refine Scheme.IdealSheafData.ext ?_
  funext P
  have hQaff : IsAffineOpen (Scheme.Opens.ι U ''ᵁ P.1) :=
    P.2.image_of_isOpenImmersion (Scheme.Opens.ι U)
  have hpre : Scheme.Opens.ι U ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι U).preimage_image_eq P.1
  have e : P.1 ≤ Scheme.Opens.ι U ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1) := hpre.ge
  have hQU : (Scheme.Opens.ι U ''ᵁ P.1) ≤ U := Scheme.Opens.ι_image_le ..
  have hmono : (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) ≤ (Z.subschemeι ⁻¹ᵁ U) :=
    fun x hx => hQU hx
  have hOW : (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) ≤ W := le_trans hmono hU
  have hinjW := injective_app_opensι_of_le W (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)) hOW
  have hkerA : RingHom.ker (CommRingCat.Hom.hom
        ((openSubschemeKer Z W).subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1)))
      = RingHom.ker (CommRingCat.Hom.hom
        ((Scheme.Opens.ι W ≫ Z.subschemeι).app (Scheme.Opens.ι U ''ᵁ P.1))) := by
    have h1 := AlgebraicGeometry.Scheme.Hom.ker_apply (openSubschemeKer Z W).subschemeι
      ⟨Scheme.Opens.ι U ''ᵁ P.1, hQaff⟩
    have h2 := AlgebraicGeometry.Scheme.Hom.ker_apply (Scheme.Opens.ι W ≫ Z.subschemeι)
      ⟨Scheme.Opens.ι U ''ᵁ P.1, hQaff⟩
    rw [Scheme.IdealSheafData.ker_subschemeι] at h1
    rw [← h1, ← h2, openSubschemeKer_eq_ker]
  have hmain : RingHom.ker (CommRingCat.Hom.hom
        ((openSubschemeKer Z W).subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1)))
      = RingHom.ker (CommRingCat.Hom.hom
        (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1))) := by
    rw [hkerA]
    ext x
    have hfac : (CommRingCat.Hom.hom
          ((Scheme.Opens.ι W ≫ Z.subschemeι).app (Scheme.Opens.ι U ''ᵁ P.1))) x
        = (CommRingCat.Hom.hom ((Scheme.Opens.ι W).app
            (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1))))
          ((CommRingCat.Hom.hom (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1))) x) := by
      show (CommRingCat.Hom.hom (Z.subschemeι.app (Scheme.Opens.ι U ''ᵁ P.1) ≫
        (Scheme.Opens.ι W).app (Z.subschemeι ⁻¹ᵁ (Scheme.Opens.ι U ''ᵁ P.1)))) x = _
      rw [CommRingCat.hom_comp, RingHom.comp_apply]
    simp only [RingHom.mem_ker, hfac]
    constructor
    · intro hx
      exact hinjW (hx.trans (map_zero _).symm)
    · intro hx
      exact (congrArg _ hx).trans (map_zero _)
  rw [AlgebraicGeometry.Scheme.Hom.ker_apply ((openSubschemeKer Z W).subschemeι ∣_ U) P,
    AlgebraicGeometry.Scheme.Hom.ker_apply (Z.subschemeι ∣_ U) P,
    ker_app_morphismRestrict_eq_map_ker (openSubschemeKer Z W).subschemeι U P e,
    ker_app_morphismRestrict_eq_map_ker Z.subschemeι U P e, hmain]
end FunctorialResolution.EmbeddedResolution
