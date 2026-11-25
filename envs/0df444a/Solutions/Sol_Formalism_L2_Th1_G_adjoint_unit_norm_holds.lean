-- Prove2me | solution 1 for Formalism.L2.Th1.G.adjoint_unit_norm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:59.692075+00:00
-- url     : https://prove2.me/submissions/d43fab48-48f2-4ce6-927f-9c7d2f185841

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_L2_Th1_G_inverse_endo_integral_holds
import Theorems.Thm_Formalism_L2_Th1_C_adjFromNorm
import Theorems.Thm_Formalism_L2_Th1_C_zLinInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
namespace Formalism.L2.Th1.G
theorem _root_.solution : AdjUnitNorm := by
  intro K _ _ R l linv ph a b N hFr hF1 ha hai hEa hEb hN hPh
  refine adjFromNorm K R l linv ph a b hFr ha hEa (inverse_endo_integral_holds K R l linv a hFr.1 ha hai hEa) hEb
    hPh ?_
  rw [hN]
  exact zLinInt K R l linv ph hFr hF1 N
end Formalism.L2.Th1.G
