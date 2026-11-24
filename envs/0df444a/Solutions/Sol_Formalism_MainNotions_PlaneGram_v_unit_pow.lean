-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_unit_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:38.237234+00:00
-- url     : https://prove2.me/submissions/28516237-feb3-4e9b-ba1f-553bb6eaeb98

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
theorem _root_.solution {x : K} (h : v x = 0) (n : ℕ) : v (x ^ n) = 0 := by
  rw [AddValuation.map_pow, h, nsmul_zero]
end Formalism.MainNotions.PlaneGram
