-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.one_le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:15.185737+00:00
-- url     : https://prove2.me/submissions/af9a68a1-8c75-423a-9320-11e1dbfb6e3e

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
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z) (h0 : f z = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z := by
  rw [han.meromorphicOrderAt_eq]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 1) han).mpr fun i hi ↦ ?_)
  interval_cases i
  simpa using h0
end Formalism.L2.Th1.F.ThreeTermRelation
