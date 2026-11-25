-- Prove2me | solution 1 for Formalism.L2.Th1.B.Cor.sigma_one_cocycle_shifted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:11:19.631864+00:00
-- url     : https://prove2.me/submissions/4fe6e287-7e41-4366-b344-dc1b7e6fe026

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SigmaOneCocycleShifted
import Theorems.Thm_Formalism_L2_Th1_B_f1E
import Theorems.Thm_Formalism_L2_Th1_B_wIntegral
import Theorems.Thm_Formalism_L2_Th1_B_wOfWp


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
theorem _root_.solution : SigmaOneCocycleShifted := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hi hC hc hk h2
  have hW := wOfWp K g2 g3 e1 P hP he
  have hw := (wIntegral K c0 e1 P l i ep F hF hC hc).2
  obtain ⟨a, -, b, c⟩ := f1E K (3 * e1) (3 * e1 ^ 2 - g2 / 4) e1 s2 (wOf e1 P) l i F hW hF hi hk hw h2
  exact ⟨a, b, c⟩
end Formalism.L2.Th1.B.Cor
