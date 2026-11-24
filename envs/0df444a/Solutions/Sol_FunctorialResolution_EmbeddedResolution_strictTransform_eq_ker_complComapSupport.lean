-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_complComapSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:23.106268+00:00
-- url     : https://prove2.me/submissions/743769a6-9d39-4b69-872a-ab8dcdeac54e

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
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformImmersion_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformOpens_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransform_eq_ker
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_complComapSupport_eq
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10


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
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D =
      Scheme.Hom.ker
        (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι ≫
          Scheme.Opens.ι (complComapSupport π Z)) := by
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq,
    ← complComapSupport_eq]
  exact ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)
end FunctorialResolution.EmbeddedResolution
