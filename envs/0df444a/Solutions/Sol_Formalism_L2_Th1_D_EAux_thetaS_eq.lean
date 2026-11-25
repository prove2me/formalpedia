-- Prove2me | solution 1 for Formalism.L2.Th1.D.EAux.thetaS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:02.562591+00:00
-- url     : https://prove2.me/submissions/52b1cd45-3e0d-44b0-b58b-1d4640467186

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_L2_Th1_A_uSerEq


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp BHyp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog BetaHyp)
open Formalism.L2.Th1.A (shortW logSer expSer fgl wpReg iSer xS IntModel)
open Formalism.L2.Th1.B (fLog lU sigS phO)
open Formalism.L2.Th1.D.EAux
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.D.EAux
theorem _root_.solution (l : ℕ) (g2 g3 ε : K) :
    thetaS l g2 g3 ε = PowerSeries.subst (PowerSeries.C ε * lgF K l) (expSer (shortW g2 g3)) := by
  unfold thetaS
  rw [Formalism.L2.Th1.A.uSerEq K g2 g3]
end Formalism.L2.Th1.D.EAux
