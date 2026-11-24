-- Prove2me | solution 1 for FunctorialResolution.Blowup.sectionsRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:12:22.6288+00:00
-- url     : https://prove2.me/submissions/edf80155-4b4d-43ea-b770-3f353db95f83

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages

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
namespace FunctorialResolution.Blowup
theorem _root_.solution {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) (r : A) :
    sectionsRingHom g V r =
      (g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) := rfl
end FunctorialResolution.Blowup
