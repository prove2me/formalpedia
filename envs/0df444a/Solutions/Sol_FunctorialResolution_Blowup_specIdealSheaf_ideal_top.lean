-- Prove2me | solution 1 for FunctorialResolution.Blowup.specIdealSheaf_ideal_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:56.082801+00:00
-- url     : https://prove2.me/submissions/12fe33ec-6e8c-4c45-9d9a-9072ff8120f1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_ideal_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I :=
  Scheme.IdealSheafData.ofIdealTop_ideal_top _
end FunctorialResolution.Blowup
