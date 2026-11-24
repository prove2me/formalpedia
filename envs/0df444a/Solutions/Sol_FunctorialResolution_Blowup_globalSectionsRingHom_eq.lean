-- Prove2me | solution 1 for FunctorialResolution.Blowup.globalSectionsRingHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:51.575401+00:00
-- url     : https://prove2.me/submissions/557913f6-9b01-4591-8e13-6a3bd9a11404

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u v
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) :
    globalSectionsRingHom g = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom := rfl
end FunctorialResolution.Blowup
