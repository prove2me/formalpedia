-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.restrictToSubscheme_coordIdeal_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:38:14.661565+00:00
-- url     : https://prove2.me/submissions/9d0100dd-11ca-4ecf-8832-f80105405402

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_top_eq_map_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_ideal_top
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem presheaf_map_comp_eq {W : Scheme.{u}} {A B C : (Opens ↥W)ᵒᵖ}
    (α : A ⟶ B) (β : B ⟶ C) (γ : A ⟶ C) :
    W.presheaf.map α ≫ W.presheaf.map β = W.presheaf.map γ :=
  (W.presheaf.map_comp α β).symm.trans
    (congrArg W.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
private theorem opens_ι_appLE_top_eq_topIso_inv {W : Scheme.{u}} (V : W.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp [Scheme.Hom.appLE]
  exact presheaf_map_comp_eq _ _ _
private theorem restrictToSubscheme_map_appTop_coord (c : EtaleChart p U m)
    (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S)
    (i : Fin (m - S.card)) :
    ((c.restrictToSubscheme hU Z S h).map.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) =
      (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i))) := by
  simp [EtaleChart.restrictToSubscheme, EtaleChart.ofCoords_map,
    EtaleChart.restrictToSubschemeCoords]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z : X.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) (i : Fin (m - S.card)) (E : X.IdealSheafData)
    (hE : restrictIdeal E U = c.coordIdeal {complOrderEmb m S i}) :
    restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU Z S h).coordIdeal {i} := by
  have hVaff : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U) := isAffineOpen_preimage_subschemeι Z hU
  have hVa : IsAffine (Z.subschemeι ⁻¹ᵁ U).toScheme := hVaff
  have hAa : IsAffine (affineSpaceFin k (m - S.card)) := inferInstance
  have e1 : (⊤ : ((Z.subschemeι ⁻¹ᵁ U).toScheme).Opens) ≤
      (Z.subschemeι ⁻¹ᵁ U).ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U) := by simp
  have hL1 : (restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((Z.subschemeι ⁻¹ᵁ U).ι.appLE (Z.subschemeι ⁻¹ᵁ U) ⊤ e1).hom
        ((E.comap Z.subschemeι).ideal ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE (E.comap Z.subschemeι)
      (Z.subschemeι ⁻¹ᵁ U).ι ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩ ⟨⊤, isAffineOpen_top _⟩ e1
  have hL2 : (E.comap Z.subschemeι).ideal ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩ =
      Ideal.map (Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (E.ideal ⟨U, hU⟩) :=
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE E Z.subschemeι ⟨U, hU⟩
      ⟨Z.subschemeι ⁻¹ᵁ U, hVaff⟩ le_rfl
  have hL3 : E.ideal ⟨U, hU⟩ = Ideal.span {c.coord (complOrderEmb m S i)} := by
    rw [c.ideal_eq_span_coord hU E {complOrderEmb m S i} hE, Finset.coe_singleton,
      Set.image_singleton]
  have hR1 : ((c.restrictToSubscheme hU Z S h).coordIdeal {i}).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map ((c.restrictToSubscheme hU Z S h).map.appTop).hom
        ((coordSubspaceIdeal k (m - S.card) {i}).ideal ⟨⊤, isAffineOpen_top _⟩) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
    exact Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop _ _
  have hR2 : (coordSubspaceIdeal k (m - S.card) {i}).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)} := by
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.ofIdealTop_ideal_top, Finset.coe_singleton,
      Set.image_singleton]
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  show (restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U)).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
    ((c.restrictToSubscheme hU Z S h).coordIdeal {i}).ideal ⟨⊤, isAffineOpen_top _⟩
  rw [hL1, hL2, hL3, hR1, hR2]
  simp only [Ideal.map_span, Set.image_singleton]
  rw [restrictToSubscheme_map_appTop_coord, opens_ι_appLE_top_eq_topIso_inv]
end EtaleChart
end FunctorialResolution.EmbeddedResolution
