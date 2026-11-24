-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVC.exists_unitK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:39:02.495817+00:00
-- url     : https://prove2.me/submissions/efebb175-ba3c-4aa4-b2d5-f270d7b2ba0b

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
theorem _root_.solution (v : (𝓞 (cmF K))ˣ) : ∃ w : (𝓞 K)ˣ, algebraMap (𝓞 K) K (w : 𝓞 K) = iota K v :=
  ⟨Units.map (RingOfIntegers.mapRingHom ((cmF K).val.toRingHom)).toMonoidHom v, rfl⟩
end Formalism.MainNotions.BridgeLemVC
