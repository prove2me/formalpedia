-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.toR_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:37.915642+00:00
-- url     : https://prove2.me/submissions/d200a0a4-9c3a-4f49-9f0c-a492f1e06fe6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (n : ℤ) : toR (n : WithTop ℤ) = (((n : ℤ) : ℝ) : WithTop ℝ) := rfl
end Formalism.MainNotions.PlaneGram
