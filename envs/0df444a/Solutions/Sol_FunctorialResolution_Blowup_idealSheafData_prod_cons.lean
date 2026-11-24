-- Prove2me | solution 1 for FunctorialResolution.Blowup.idealSheafData_prod_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:45.456953+00:00
-- url     : https://prove2.me/submissions/41956557-0953-4a72-9096-9f2064cc7a29

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData

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
theorem _root_.solution (X : Scheme.{u}) (D : X.IdealSheafData)
    (E : List X.IdealSheafData) : (D :: E).prod = D * E.prod :=
  List.prod_cons
end FunctorialResolution.Blowup
