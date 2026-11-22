-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:16.719045+00:00
-- url     : https://prove2.me/submissions/ab49bae7-9ff3-4bd8-9789-e4bf2a1bff44

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
theorem _root_.solution {a b : ℝ} {x : K} (h : b ≤ a) (hx : vge v a x) : vge v b x := by
  unfold vge at *
  exact le_trans (WithTop.coe_le_coe.mpr h) hx
end Formalism.MainNotions.PlaneGram
