-- Prove2me | solution 1 for FunctorialResolution.Blowup.idealSheafData_prod_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:45.817233+00:00
-- url     : https://prove2.me/submissions/e32273c9-2e64-435a-ad5c-624d2d1f0e9c

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
theorem _root_.solution (X : Scheme.{u}) :
    ([] : List X.IdealSheafData).prod = ⊤ := by
  rw [List.prod_nil]
  rfl
end FunctorialResolution.Blowup
