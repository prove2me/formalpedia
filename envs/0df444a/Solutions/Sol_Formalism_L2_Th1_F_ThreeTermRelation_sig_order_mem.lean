-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.sig_order_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:29.250155+00:00
-- url     : https://prove2.me/submissions/55575b8d-c84d-4e27-a007-6ed30a4511d3

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
theorem _root_.solution (hord : SigmaOrder) {β z : ℂ} (h : z + β ∈ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L (w + β)) z = ((1 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp only [one_mul] at this
  rw [this, if_pos (by rwa [one_mul])]
  rfl
end Formalism.L2.Th1.F.ThreeTermRelation
