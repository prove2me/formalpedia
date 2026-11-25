-- Prove2me | solution 1 for Formalism.L2.Th1.D.EAux.subst_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:58.260631+00:00
-- url     : https://prove2.me/submissions/d0d9b735-832c-4218-b1f3-e4c84d65386b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
theorem _root_.solution {τ : Type} {b : MvPowerSeries τ K} (hb : MvPowerSeries.constantCoeff b = 0)
    (c : K) (f : PowerSeries K) :
    PowerSeries.subst b (PowerSeries.C c * f) = MvPowerSeries.C c * PowerSeries.subst b f := by
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hb), PowerSeries.subst_C]
end Formalism.L2.Th1.D.EAux
