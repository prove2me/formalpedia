-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sectionsRingHom_sub_mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:27:38.883187+00:00
-- url     : https://prove2.me/submissions/2a3d93cd-7209-4a2c-a610-e373dcd57a37

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
import Theorems.Thm_FunctorialResolution_Blowup_sectionsRingHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


section
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
universe u
section
variable {B A : Type u} [CommRing B] [CommRing A]
end
section
variable {R : Type u} [CommRing R]
end
section
variable {R : Type u} [CommRing R]
private theorem sectionsRingHom_comp {A : Type u} [CommRing A] {Z W : Scheme.{u}} (p : Z ⟶ W)
    (ρ : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) (V' : Z.Opens)
    (hle : V' ≤ (Opens.map p.base).obj V) (r : A) :
    Blowup.sectionsRingHom (p ≫ ρ) V' r
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE p V V' hle)) (Blowup.sectionsRingHom ρ V r) := by
  rw [Blowup.sectionsRingHom_apply, Blowup.sectionsRingHom_apply]
  conv_rhs => rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
private theorem mem_ideal_of_app_subschemeι_eq_zero {W : Scheme.{u}} (𝔞 : W.IdealSheafData) (V : W.affineOpens)
    (x : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hx : (CommRingCat.Hom.hom (Scheme.Hom.app 𝔞.subschemeι (V : W.Opens))) x = 0) :
    x ∈ 𝔞.ideal V := by
  rw [Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply] at hx
  have h2 := congrArg (CommRingCat.Hom.hom (𝔞.subschemeObjIso V).hom) hx
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id] at h2
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h2
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A : Type u} [CommRing A] {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of A)) (𝔞 : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (V : W.affineOpens) (r : A) :
    Blowup.sectionsRingHom ρ (V : W.Opens) r - Blowup.sectionsRingHom ρ' (V : W.Opens) r ∈ 𝔞.ideal V := by
  apply mem_ideal_of_app_subschemeι_eq_zero
  have h1 : Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ)
        ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r
      = Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ')
        ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r := by
    rw [hagree]
  rw [sectionsRingHom_comp 𝔞.subschemeι ρ (V : W.Opens) _ le_rfl r,
    sectionsRingHom_comp 𝔞.subschemeι ρ' (V : W.Opens) _ le_rfl r] at h1
  rw [Scheme.Hom.app_eq_appLE, map_sub, h1]
  exact sub_self _
end FunctorialResolution.EmbeddedResolution
