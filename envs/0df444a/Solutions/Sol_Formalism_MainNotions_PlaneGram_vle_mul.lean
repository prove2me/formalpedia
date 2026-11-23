-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vle_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:33.508025+00:00
-- url     : https://prove2.me/submissions/24a3031b-7c7b-4288-898e-63baf1864fec

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vR_mul

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
theorem _root_.solution {a b : ℝ} {x y : K} (hx : vle v a x) (hy : vle v b y) : vle v (a + b) (x * y) := by
  unfold vle at *
  rw [vR_mul, WithTop.coe_add]
  exact add_le_add hx hy
end Formalism.MainNotions.PlaneGram
