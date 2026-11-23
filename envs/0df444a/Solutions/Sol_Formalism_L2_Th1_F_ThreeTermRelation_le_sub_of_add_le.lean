-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.le_sub_of_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:50.923822+00:00
-- url     : https://prove2.me/submissions/d1c4cf1f-e72e-4434-b5b3-0aef389d679e

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
namespace Formalism.L2.Th1.F.ThreeTermRelation
theorem _root_.solution {o : WithTop ℤ} {m k : ℤ} (h : ((k + m : ℤ) : WithTop ℤ) ≤ o) :
    (k : WithTop ℤ) ≤ o - (m : WithTop ℤ) := by
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have := WithTop.coe_le_coe.1 h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_le_coe.2 (by omega)
end Formalism.L2.Th1.F.ThreeTermRelation
