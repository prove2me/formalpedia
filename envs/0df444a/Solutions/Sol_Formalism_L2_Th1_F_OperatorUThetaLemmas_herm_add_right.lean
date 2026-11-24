-- Prove2me | solution 1 for Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:25:01.710808+00:00
-- url     : https://prove2.me/submissions/f392d2fe-c1e4-4a97-abaa-01088ae7edd7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OperatorUComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.OperatorUThetaLemmas
namespace Formalism.L2.Th1.F.OperatorUThetaLemmas
theorem _root_.solution (L : PeriodPair) (w x y : ℂ) :
    herm L w (x + y) = herm L w x + herm L w y := by
  simp only [Formalism.L2.Th1.F.herm, map_add]
  ring
end Formalism.L2.Th1.F.OperatorUThetaLemmas
