-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.iota_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:15.926795+00:00
-- url     : https://prove2.me/submissions/9dd1ae75-4f0f-4c61-b9a0-6ee6dbeaa2d9

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVN
theorem _root_.solution (x : (𝓞 (cmF K))ˣ) : iota K x ≠ 0 := by
  intro h0
  have := congrArg (iota K) (mul_inv_cancel x)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this
end Formalism.MainNotions.BridgeLemVN
