-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:43.059298+00:00
-- url     : https://prove2.me/submissions/ecc07d0a-9ee8-4ff0-82b3-f9526642e646

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {x y : K} (hx : 0 ≤ v x) (hy : 0 ≤ v y) : 0 ≤ v (x * y) := by
  rw [AddValuation.map_mul]
  exact add_nonneg hx hy
end Formalism.MainNotions.PlaneGram
