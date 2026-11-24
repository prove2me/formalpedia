-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vle_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:35.784074+00:00
-- url     : https://prove2.me/submissions/0e2db875-b681-4041-b8e0-d1f2d43433d9

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
theorem _root_.solution {a b : ℝ} {x : K} (h : a ≤ b) (hx : vle v a x) : vle v b x := by
  unfold vle at *
  exact le_trans hx (WithTop.coe_le_coe.mpr h)
end Formalism.MainNotions.PlaneGram
