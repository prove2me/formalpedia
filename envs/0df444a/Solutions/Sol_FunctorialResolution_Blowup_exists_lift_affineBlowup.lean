-- Prove2me | solution 1 for FunctorialResolution.Blowup.exists_lift_affineBlowup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:29.062525+00:00
-- url     : https://prove2.me/submissions/607305b4-13db-4f3d-889a-952caa83bbaa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Theorems.Thm_FunctorialResolution_Blowup_reesAlgebraLift_algebraMap
import Theorems.Thm_FunctorialResolution_Blowup_globalSectionsRingHom_eq
import Theorems.Thm_FunctorialResolution_Blowup_affineBlowupChart_comp_toSpec
import Theorems.Thm_FunctorialResolution_Blowup_algebraMap_chart_eq_chartRingHom
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_apply
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_coe_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


section
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.Blowup
universe u v
section
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
end
section
variable {R : Type u} [CommRing R]
private theorem homogeneousLocalizationAwayVal_apply {B : Type u} [CommRing B] (J : Ideal B) (a : ↥J)
    (p : HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a)) :
    homogeneousLocalizationAwayVal J a p = HomogeneousLocalization.val p := rfl
private theorem homogeneousAwayLift_chartRingHom {B : Type u} [CommRing B] (J : Ideal B)
    {T : Type v} [CommRing T] (φ : B →+* T) (a : ↥J)
    (hgen : Ideal.map φ J = Ideal.span {φ (a : B)})
    (hnzd : φ (a : B) ∈ nonZeroDivisors T) (r : B) :
    homogeneousAwayLift J φ a hgen hnzd (chartRingHom J a r) = φ r := by
  have hcoe : ((algebraMap B ↥(reesAlgebra J) r : ↥(reesAlgebra J)) : Polynomial B)
      = Polynomial.C r := rfl
  have h1 : ((reesDegreeZeroEquiv J r : ↥(reesGrading J 0)) : ↥(reesAlgebra J))
      = algebraMap B ↥(reesAlgebra J) r := by
    apply Subtype.ext
    rw [reesDegreeZeroEquiv_coe_coe, hcoe]
  have hz : HomogeneousLocalization.val
        (HomogeneousLocalization.fromZeroRingHom (reesGrading J)
          (Submonoid.powers (reesGenerator J a)) (reesDegreeZeroEquiv J r))
      = Localization.mk ((reesDegreeZeroEquiv J r : ↥(reesGrading J 0)) : ↥(reesAlgebra J)) 1 := rfl
  have hval : HomogeneousLocalization.val (chartRingHom J a r)
      = algebraMap ↥(reesAlgebra J) (Localization.Away (reesGenerator J a))
          (algebraMap B ↥(reesAlgebra J) r) := by
    rw [chartRingHom_apply, hz, h1, Localization.mk_one_eq_algebraMap]
  unfold homogeneousAwayLift
  rw [RingHom.comp_apply, homogeneousLocalizationAwayVal_apply, hval, IsLocalization.lift_eq,
    reesAlgebraLift_algebraMap]
end
end FunctorialResolution.Blowup
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u v
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) {W : Scheme.{u}} [IsAffine W]
    (g : W ⟶ Spec (CommRingCat.of R)) (a : ↥I)
    (hgen : Ideal.map (globalSectionsRingHom g) I = Ideal.span {globalSectionsRingHom g (a : R)})
    (hnzd : globalSectionsRingHom g (a : R) ∈ nonZeroDivisors Γ(W, ⊤)) :
    ∃ h : W ⟶ affineBlowup I,
      h ≫ AffineBlowup.toSpec I = g ∧
        Set.range h.base ⊆ Set.range (affineBlowupChart I a).base := by
  refine ⟨W.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (homogeneousAwayLift I (globalSectionsRingHom g) a hgen hnzd)) ≫
        affineBlowupChart I a, ?_, ?_⟩
  · have h2 : affineBlowupChart I a ≫ AffineBlowup.toSpec I
        = Spec.map (CommRingCat.ofHom (chartRingHom I a)) := by
      rw [affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
    have h3 : CommRingCat.ofHom (chartRingHom I a) ≫
          CommRingCat.ofHom (homogeneousAwayLift I (globalSectionsRingHom g) a hgen hnzd)
        = CommRingCat.ofHom (globalSectionsRingHom g) := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom
        (RingHom.ext fun r => homogeneousAwayLift_chartRingHom I (globalSectionsRingHom g) a hgen hnzd r)
    have nat : W.toSpecΓ ≫ Spec.map g.appTop = g ≫ (Spec (CommRingCat.of R)).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality]
    have tri : (Spec (CommRingCat.of R)).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = 𝟙 (Spec (CommRingCat.of R)) := by
      simp
    rw [Category.assoc, Category.assoc, h2, ← Spec.map_comp, h3, globalSectionsRingHom_eq,
      CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, nat, Category.assoc, tri,
      Category.comp_id]
  · rintro x ⟨w, rfl⟩
    exact ⟨(W.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (homogeneousAwayLift I (globalSectionsRingHom g) a hgen hnzd))).base w,
      by simp⟩
end FunctorialResolution.Blowup
