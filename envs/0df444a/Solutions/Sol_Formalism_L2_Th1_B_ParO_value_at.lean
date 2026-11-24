-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.value_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:18.794857+00:00
-- url     : https://prove2.me/submissions/40eb3c1e-299f-4626-8961-6f2710e8a8b4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution {ι : Type} {l g ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hph : PowerSeries.constantCoeff ph = 0)
    (e : PowerSeries.subst l g = PowerSeries.X * fExp (-ph))
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst (PowerSeries.subst U l) g = U * fExp (-PowerSeries.subst U ph) := by
  have hlS := PowerSeries.HasSubst.of_constantCoeff_zero' hl
  have hUS := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hph, neg_zero]
  rw [← PowerSeries.subst_comp_subst_apply hlS hUS, e, PowerSeries.subst_mul hUS,
    PowerSeries.subst_X hUS, psubst_fExp hU hnph, psubst_neg hU]
end Formalism.L2.Th1.B.ParO
