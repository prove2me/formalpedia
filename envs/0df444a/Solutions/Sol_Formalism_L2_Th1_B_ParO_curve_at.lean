-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.curve_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:23.360815+00:00
-- url     : https://prove2.me/submissions/f958dab6-5cff-40b0-8b6a-82033dd8b636

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_psubst_one


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
theorem _root_.solution {ι : Type} {l P ep : PowerSeries K} {c0 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) (x : ι) :
    MvPowerSeries.X x ^ 2 * (1 + at1 x l ^ 2 * PowerSeries.subst (at1 x l) P) =
      at1 x l ^ 2 * (at1 x ep + MvPowerSeries.C c0 * MvPowerSeries.X x ^ 2) := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have hlS := PowerSeries.HasSubst.of_constantCoeff_zero' hl
  have h2 := congrArg (fun φ : PowerSeries K => PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) φ) h
  simp only [PowerSeries.subst_mul hX, PowerSeries.subst_add hX, PowerSeries.subst_pow hX,
    Formalism.L2.Th1.B.psubst_one hX, PowerSeries.subst_X hX, PowerSeries.subst_C,
    PowerSeries.subst_comp_subst_apply hlS hX] at h2
  exact h2
end Formalism.L2.Th1.B.ParO
