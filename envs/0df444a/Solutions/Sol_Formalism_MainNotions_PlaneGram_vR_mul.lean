-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:29.010477+00:00
-- url     : https://prove2.me/submissions/b4ab5c16-1939-4421-8cb9-46af3bd2f187

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
theorem _root_.solution (x y : K) : vR v (x * y) = vR v x + vR v y := by
  unfold vR
  rw [AddValuation.map_mul]
  cases h1 : v x <;> cases h2 : v y
  · simp
  · simp
  · simp
  · rw [← WithTop.coe_add, WithTop.map_coe, WithTop.map_coe, WithTop.map_coe, Rat.cast_add,
      WithTop.coe_add]
end Formalism.MainNotions.PlaneGram
