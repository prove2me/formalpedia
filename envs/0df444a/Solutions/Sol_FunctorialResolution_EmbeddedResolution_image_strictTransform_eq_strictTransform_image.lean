-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.image_strictTransform_eq_strictTransform_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:58:16.629424+00:00
-- url     : https://prove2.me/submissions/468b81ea-6baa-4ad7-9971-d2f068c710bb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_map_eq_ker_subscheme__comp_8e2f1045f336
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_subscheme__comp_eq_of_ker_le_9ee7054b5bee
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_complComapSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_preimage_complComapSupport_eq
import Theorems.Thm_FunctorialResolution_Blowup_comap_map_of_isClosedImmersion
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_morphismRestrict_3254f25617a8
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem map_ker_subschemeι_comp_restrict {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j]
    (D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁) [IsClosedImmersion j₁]
    (hsq : j₁ ≫ π' = π ≫ j) (V' : A'₁.Opens) [IsClosedImmersion (j₁ ∣_ V')]
    (hkerr : Scheme.Hom.ker (j₁ ∣_ V') ≤
      ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) :
    (Scheme.Hom.ker (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι)).map j₁
      = Scheme.Hom.ker
          ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι ≫ V'.ι) := by
  have hm : (j₁ ∣_ V') ≫ V'.ι ≫ π' = (j₁ ⁻¹ᵁ V').ι ≫ π ≫ j := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hsq]
  have hMcomap :
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
    calc ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ∣_ V') ≫ V'.ι ≫ π') := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ∣_ V') (V'.ι ≫ π'),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) V'.ι π']
      _ = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ⁻¹ᵁ V').ι ≫ π ≫ j) := by rw [hm]
      _ = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ⁻¹ᵁ V').ι (π ≫ j),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) π j,
            ← map_eq_ker_subschemeι_comp j D, Blowup.comap_map_of_isClosedImmersion j D]
  have hmor : ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι) ≫ j₁)
      = ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) ≫ V'.ι) := by
    simp only [Category.assoc, morphismRestrict_ι]
  rw [← Scheme.Hom.ker_comp, hmor,
    Scheme.Hom.ker_comp (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) V'.ι,
    ker_subschemeι_comp_eq_of_ker_le (j₁ ∣_ V')
      (((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) hkerr
      ((D.comap π).comap (j₁ ⁻¹ᵁ V').ι) hMcomap.symm,
    Scheme.Hom.ker_comp
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι) V'.ι,
    Scheme.IdealSheafData.ker_subschemeι]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁]
    (hsq : j₁ ≫ π' = π ≫ j)
    (hker : Scheme.Hom.ker j₁ =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j)) (Scheme.Hom.ker j)) :
    Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker (D.subschemeι ≫ j)) := by
  have : IsClosedImmersion
      (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) := inferInstance
  have hDle : Scheme.Hom.ker j ≤ Scheme.Hom.ker (D.subschemeι ≫ j) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      ← Scheme.IdealSheafData.map_bot j]
    exact Scheme.IdealSheafData.map_mono j bot_le
  have hUeq : j₁ ⁻¹ᵁ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
      = complComapSupport π Z := preimage_complComapSupport_eq j Z π π' j₁ hsq
  have hkerr : Scheme.Hom.ker (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))
      ≤ ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap
          (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι := by
    rw [← ker_comap_ι_eq_ker_morphismRestrict j₁
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))), hker,
      strictTransform_comap_complComapSupport_ι π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker j)]
    exact Scheme.IdealSheafData.comap_mono
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι
      (Scheme.IdealSheafData.comap_mono π' hDle)
  have hTmap : Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁)
      = (Blowup.strictTransform π Z D).map j₁ := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  rw [hTmap, strictTransform_eq_ker_complComapSupport π Z D, ← hUeq,
    map_ker_subschemeι_comp_restrict j D π π' j₁ hsq
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) hkerr]
  exact (strictTransform_eq_ker_complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
    (Scheme.Hom.ker (D.subschemeι ≫ j))).symm
end FunctorialResolution.EmbeddedResolution
