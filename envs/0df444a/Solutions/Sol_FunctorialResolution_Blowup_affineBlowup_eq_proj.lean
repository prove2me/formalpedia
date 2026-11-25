-- Prove2me | solution 1 for FunctorialResolution.Blowup.affineBlowup_eq_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:41.163211+00:00
-- url     : https://prove2.me/submissions/34450683-793c-44e4-86aa-3b53a9c4fc20

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) :
    affineBlowup I = AlgebraicGeometry.Proj (reesGrading I) := rfl
end FunctorialResolution.Blowup
