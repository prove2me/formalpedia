-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.subst_wpDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:17.666271+00:00
-- url     : https://prove2.me/submissions/5e460a1c-fbcf-43f6-82b2-bf47a9534bfe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_inVar

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
theorem _root_.solution {ι : Type} (P : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (wpDiff P) =
      b 0 ^ 2 - b 1 ^ 2 +
        b 0 ^ 2 * b 1 ^ 2 * (PowerSeries.subst (b 1) P - PowerSeries.subst (b 0) P) := by
  rw [Formalism.L2.Th1.B.wpDiff]
  simp only [MvPowerSeries.subst_add hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_mul hb,
    MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb, subst_inVar P 0 hb, subst_inVar P 1 hb]
end Formalism.L2.Th1.B.ParO
