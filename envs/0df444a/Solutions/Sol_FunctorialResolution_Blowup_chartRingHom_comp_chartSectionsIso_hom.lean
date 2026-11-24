-- Prove2me | solution 1 for FunctorialResolution.Blowup.chartRingHom_comp_chartSectionsIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:14:09.921877+00:00
-- url     : https://prove2.me/submissions/c4fd1213-ddc5-41a1-89c2-1168506208e8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Theorems.Thm_FunctorialResolution_Blowup_chartSectionsIso_hom
import Theorems.Thm_FunctorialResolution_Blowup_affineBlowupChart_comp_toSpec
import Theorems.Thm_FunctorialResolution_Blowup_algebraMap_chart_eq_chartRingHom
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


section
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
private theorem comp_presheaf_map_eq_of_heq {Z : Scheme.{u}} {A : CommRingCat.{u}} (U : Z.Opens) (hU : U = ⊤)
    (φ : A ⟶ Γ(Z, U)) (h : (⊤ : Z.Opens) ≤ U) (ψ : A ⟶ Γ(Z, (⊤ : Z.Opens)))
    (hφ : HEq φ ψ) : φ ≫ Z.presheaf.map (homOfLE h).op = ψ := by
  subst hU
  obtain rfl : φ = ψ := eq_of_heq hφ
  rw [show (homOfLE h : (⊤ : Z.Opens) ⟶ ⊤) = 𝟙 (⊤ : Z.Opens) from rfl]
  simp
private theorem appTop_eq_appLE_top_top {Z S : Scheme.{u}} (f : Z ⟶ S)
    (h : (⊤ : Z.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) : f.appLE ⊤ ⊤ h = f.appTop :=
  comp_presheaf_map_eq_of_heq (f ⁻¹ᵁ (⊤ : S.Opens)) (le_antisymm le_top h) (f.app ⊤) h f.appTop HEq.rfl
private theorem appLE_image_top_comp_appIso_hom {Z X S : Scheme.{u}} (g : Z ⟶ X)
    [IsOpenImmersion g] (p : X ⟶ S)
    (e : (g ''ᵁ (⊤ : Z.Opens)) ≤ p ⁻¹ᵁ (⊤ : S.Opens)) :
    p.appLE ⊤ (g ''ᵁ ⊤) e ≫ (g.appIso ⊤).hom = (g ≫ p).appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  exact appTop_eq_appLE_top_top (g ≫ p) _
end FunctorialResolution.Blowup
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (a : ↥I) :
    CommRingCat.ofHom (chartRingHom I a) ≫ (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm) := by
  rw [chartSectionsIso_hom, ← Category.assoc, Iso.comp_inv_eq, Category.assoc,
    appLE_image_top_comp_appIso_hom, affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
  exact Scheme.ΓSpecIso_inv_naturality _
end FunctorialResolution.Blowup
