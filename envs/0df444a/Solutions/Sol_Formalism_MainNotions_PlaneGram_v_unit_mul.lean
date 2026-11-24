-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:36.513471+00:00
-- url     : https://prove2.me/submissions/a625fdf3-d929-4c18-a29f-1772e0ce3306

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {x y : K} (hx : v x = 0) (hy : v y = 0) : v (x * y) = 0 := by
  rw [v.map_mul, hx, hy, add_zero]
end Formalism.MainNotions.PlaneGram
