-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.existsUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:34.986218+00:00
-- url     : https://prove2.me/submissions/e2fcd8e8-be92-463f-92fe-3627162a5075

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (W : Scheme.{u}) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    ∃! k : W ⟶ X', k ≫ π = g :=
  h.2 W g hg
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
