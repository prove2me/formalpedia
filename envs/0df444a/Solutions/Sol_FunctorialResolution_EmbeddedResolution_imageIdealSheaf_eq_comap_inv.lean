-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.imageIdealSheaf_eq_comap_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:05.652336+00:00
-- url     : https://prove2.me/submissions/3d78f287-fb1d-4f10-a8b8-9b7a0ccd4182

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem comap_eq_ker_subschemeι_comp_inv {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    I.comap f = (I.subschemeι ≫ inv f).ker := by
  have : IsIso (Limits.pullback.snd f I.subschemeι) :=
    (IsPullback.of_hasPullback f I.subschemeι).flip.isIso_fst_of_isIso
  have hw : Limits.pullback.fst f I.subschemeι
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ inv f := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  unfold AlgebraicGeometry.Scheme.IdealSheafData.comap
  rw [hw, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
namespace IsPushforwardBlowupSeq
end IsPushforwardBlowupSeq
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    imageIdealSheaf f J = J.comap (inv f) := by
  rw [imageIdealSheaf_eq_ker, comap_eq_ker_subschemeι_comp_inv (inv f) J, IsIso.inv_inv]
end FunctorialResolution.EmbeddedResolution
