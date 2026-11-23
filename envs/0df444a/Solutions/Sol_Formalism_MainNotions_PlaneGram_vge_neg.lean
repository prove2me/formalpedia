-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:29.661312+00:00
-- url     : https://prove2.me/submissions/082d3547-1907-4a88-a167-2c07fc5a9ec6

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
theorem _root_.solution {a : ℝ} {x : K} (hx : vge v a x) : vge v a (-x) := by
  unfold vge vR at *
  rwa [AddValuation.map_neg]
end Formalism.MainNotions.PlaneGram
