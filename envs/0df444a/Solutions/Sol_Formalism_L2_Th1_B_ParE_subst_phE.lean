-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParE.subst_phE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:57.165751+00:00
-- url     : https://prove2.me/submissions/9d263553-9ded-49b2-a770-b684056d86d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_Formalism_L2_Th1_B_ParE_hsU
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B.ParE
theorem _root_.solution (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) {U : MvPowerSeries ι K}
    (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst U (phE s2 e1 kap w l) =
      -PowerSeries.subst (PowerSeries.subst U l) (sigmaOneSeries e1 kap w) +
        MvPowerSeries.C (s2 / 2) * PowerSeries.subst U l ^ 2 := by
  have ha : PowerSeries.HasSubst U := hsU hU
  have hC : PowerSeries.subst U (PowerSeries.C (s2 / 2)) = MvPowerSeries.C (s2 / 2) := by
    have h := (PowerSeries.substAlgHom ha).commutes (s2 / 2)
    rw [PowerSeries.coe_substAlgHom] at h
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using h
  unfold phE
  rw [← PowerSeries.coe_substAlgHom ha]
  simp only [map_add, map_neg, map_mul, map_pow]
  rw [PowerSeries.coe_substAlgHom ha, hC,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hl) ha]
end Formalism.L2.Th1.B.ParE
