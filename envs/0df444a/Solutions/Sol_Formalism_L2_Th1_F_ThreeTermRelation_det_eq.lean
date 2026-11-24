-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:14.040924+00:00
-- url     : https://prove2.me/submissions/a0bebd8e-b3e0-46c7-ac4d-6a2acc16c473

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
theorem _root_.solution (a : ℂ) :
    Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                  1, L.weierstrassP b, L.derivWeierstrassP b;
                  1, L.weierstrassP c, L.derivWeierstrassP c] = threeTermDet L b c a := by
  rw [Matrix.det_fin_three]
  simp [threeTermDet]
  ring
end Formalism.L2.Th1.F.ThreeTermRelation
