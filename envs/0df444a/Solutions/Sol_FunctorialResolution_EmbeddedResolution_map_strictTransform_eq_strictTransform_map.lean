-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_strictTransform_eq_strictTransform_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:17.61259+00:00
-- url     : https://prove2.me/submissions/f7064501-4aec-4f64-97a2-3d67e6366f53

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_image_strictTransform_eq_strictTransform_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hker : Scheme.Hom.ker j₁ = Blowup.strictTransform π' (Z.map j) (Scheme.Hom.ker j)) :
    (Blowup.strictTransform π Z D).map j₁ = Blowup.strictTransform π' (Z.map j) (D.map j) := by
  have hZ : Z.map j = Scheme.Hom.ker (Z.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j Z
  have hD : D.map j = Scheme.Hom.ker (D.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j D
  have hT : (Blowup.strictTransform π Z D).map j₁
      = Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) :=
    map_eq_ker_subschemeι_comp j₁ (Blowup.strictTransform π Z D)
  rw [hT, hD, hZ]
  exact image_strictTransform_eq_strictTransform_image j Z D π π' j₁ hsq (by rw [hker, hZ])
end FunctorialResolution.EmbeddedResolution
