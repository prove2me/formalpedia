-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.star_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:53:02.438179+00:00
-- url     : https://prove2.me/submissions/e858ffe5-9928-42b6-850f-3dcb084d9961

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
theorem _root_.solution (x : (𝓞 (cmF K))ˣ) : star (iota K x) = iota K x := star_coe_cmF K _
end Formalism.MainNotions.BridgeLemVN
