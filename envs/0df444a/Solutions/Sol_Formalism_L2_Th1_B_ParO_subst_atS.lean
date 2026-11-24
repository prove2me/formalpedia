-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.subst_atS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:16.510798+00:00
-- url     : https://prove2.me/submissions/da06f6e1-c2ff-4cbc-b3eb-cb9fdd7a5bab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_psubst_msubst


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
theorem _root_.solution {ι : Type} (g : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (atS g) = PowerSeries.subst (b 0 + b 1) g := by
  have h0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [Formalism.L2.Th1.B.atS, Formalism.L2.Th1.B.psubst_msubst g h0 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
end Formalism.L2.Th1.B.ParO
