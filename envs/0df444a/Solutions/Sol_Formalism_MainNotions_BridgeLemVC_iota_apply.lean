-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVC.iota_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:47:33.327708+00:00
-- url     : https://prove2.me/submissions/529e8310-7c7b-4c61-8e0a-184be342bd5f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Definitions.Def_Formalism_FlagUnipotentLattices_ArithmeticIdentityEntries
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVC
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVC
theorem _root_.solution (t : (𝓞 (cmF K))ˣ) : iota K t = (((t : 𝓞 (cmF K)) : cmF K) : K) := rfl
end Formalism.MainNotions.BridgeLemVC
