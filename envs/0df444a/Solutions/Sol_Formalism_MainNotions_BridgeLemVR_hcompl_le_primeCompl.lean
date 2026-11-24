-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.hcompl_le_primeCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:56.678061+00:00
-- url     : https://prove2.me/submissions/ff25e37e-c025-41a5-b8f3-9402674f45d7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVR
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    hcompl (K := K) p ≤ p.primeCompl := by
  have := hp.isPrime
  unfold hcompl
  rw [Submonoid.closure_le]
  intro s hs
  exact hs.1
end Formalism.MainNotions.BridgeLemVR
