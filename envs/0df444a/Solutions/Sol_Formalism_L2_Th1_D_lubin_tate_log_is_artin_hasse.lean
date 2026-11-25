-- Prove2me | solution 1 for Formalism.L2.Th1.D.lubin_tate_log_is_artin_hasse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:33.827948+00:00
-- url     : https://prove2.me/submissions/833beaa0-ac76-452f-afbc-d7fb975daea9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_LubinTateLogIsArtinHasse
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs


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
namespace Formalism.L2.Th1.D
theorem _root_.solution : LtLogIsLgF := by
  intro K _ l hl
  ext n
  unfold Formalism.L2.Th1.CM.ltLog
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · have hs := Nat.find_spec h
    conv_rhs => rw [hs]
    rw [Formalism.InvariantFactorPaths.G7.coeff_lgF_pow K hl]
  · by_contra hc
    exact h (Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero (Ne.symm hc))
end Formalism.L2.Th1.D
