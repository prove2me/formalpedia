-- Prove2me | solution 1 for Formalism.L2.Th1.D.EAux.log_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:09.188833+00:00
-- url     : https://prove2.me/submissions/a41b6f7f-1790-4a9b-a5bc-e968d325c13e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_L2_Th1_D_EAux_cc_a
import Theorems.Thm_Formalism_L2_Th1_D_EAux_thetaS_eq
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_D_Pair_ps_comp
import Theorems.Thm_Formalism_L2_Th1_D_expSpec


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
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.subst (thetaS l g2 g3 ε) (logSer (shortW g2 g3)) =
      PowerSeries.C ε * lgF K l := by
  have hE := Formalism.L2.Th1.A.expSpec K (shortW g2 g3)
  have ha := cc_a hl ε
  rw [thetaS_eq, Pair.ps_comp (τ := Unit) ha hE.1, hE.2.2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' ha)]
end Formalism.L2.Th1.D.EAux
