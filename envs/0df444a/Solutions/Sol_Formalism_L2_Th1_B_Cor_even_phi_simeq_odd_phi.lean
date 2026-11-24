-- Prove2me | solution 1 for Formalism.L2.Th1.B.Cor.even_phi_simeq_odd_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:13.190579+00:00
-- url     : https://prove2.me/submissions/f9fa284f-94a7-4a0e-ae19-b3366d9913f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SigmaOneCocycleShifted
import Theorems.Thm_Formalism_L2_Th1_B_diffPh
import Theorems.Thm_Formalism_L2_Th1_B_simeqHalf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Cor
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
namespace Formalism.L2.Th1.B.Cor
theorem _root_.solution : PhESimPhO := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hC hc h2
  exact simeqHalf K Unit _ _ h2 ((diffPh K g2 g3 s2 c0 e1 P l i ep F hP he hF hC).2 hc)
end Formalism.L2.Th1.B.Cor
