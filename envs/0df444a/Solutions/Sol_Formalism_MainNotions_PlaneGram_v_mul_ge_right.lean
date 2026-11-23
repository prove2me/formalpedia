-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_mul_ge_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:29.42333+00:00
-- url     : https://prove2.me/submissions/515aa7cf-ca63-40bd-863b-d3d5b99698a0

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
theorem _root_.solution {x y : K} {c : WithTop ℚ} (hx : 0 ≤ v x) (hy : c ≤ v y) : c ≤ v (x * y) := by
  rw [AddValuation.map_mul]
  exact le_add_of_nonneg_of_le hx hy
end Formalism.MainNotions.PlaneGram
