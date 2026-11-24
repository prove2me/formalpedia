-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVC.coe_fracU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:00.607823+00:00
-- url     : https://prove2.me/submissions/fd4f82a0-2b2e-403a-9047-eeb52c393bf7

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
theorem _root_.solution {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) :
    (((fracU hM : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M :=
  coe_fracI hM
end Formalism.MainNotions.BridgeLemVC
