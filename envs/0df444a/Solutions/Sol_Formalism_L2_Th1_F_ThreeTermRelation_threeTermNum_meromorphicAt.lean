-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermNum_meromorphicAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:51.62955+00:00
-- url     : https://prove2.me/submissions/a403a4ae-0c3f-4c5f-9cce-85cae5ffbd05

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThreeTermRelation
variable (L : PeriodPair) (b c : ℂ)
namespace Formalism.L2.Th1.F.ThreeTermRelation
theorem _root_.solution (he : SigmaEntire) (z : ℂ) : MeromorphicAt (nAux L b c) z := by
  have h4 : MeromorphicAt (wSigma L) z := ((he L).analyticAt z).meromorphicAt
  have h5 := L.meromorphic_weierstrassP z
  have h6 := L.meromorphic_derivWeierstrassP z
  unfold nAux threeTermDet
  fun_prop
end Formalism.L2.Th1.F.ThreeTermRelation
