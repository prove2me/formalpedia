-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.tau_derivative_rule_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:02.429531+00:00
-- url     : https://prove2.me/submissions/11091363-ee53-4cf0-b262-3f90261a43c7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Add0_wpDiff_eq
import Theorems.Thm_Formalism_L2_Th1_B_addSigmaLog
import Theorems.Thm_Formalism_L2_Th1_B_dqRule
import Theorems.Thm_Formalism_L2_Th1_B_mul_pd_fLog
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_one_parallelogram_defect
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_zero_parallelogram_defect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.Det
theorem _root_.solution : TauRule := by
  intro K _ _ g2 g3 P hP
  set U : MvPowerSeries (Fin 2) K := 1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P with hU
  have hU1 : MvPowerSeries.constantCoeff U = 1 := by simp [hU]
  have hW : wpDiff P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * U :=
    Formalism.L2.Th1.B.Add0.wpDiff_eq dqRule hP.2.1
  have hL : par0 (sigS P) = fLog U := addSigmaLog K g2 g3 P hP
  have e0 := mul_pd_fLog (0 : Fin 2) hU1
  have e1 := mul_pd_fLog (1 : Fin 2) hU1
  have p0 := pderiv_zero_parallelogram_defect (sigS P)
  have p1 := pderiv_one_parallelogram_defect (sigS P)
  rw [hL] at p0 p1
  have x00 : pd 0 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 1 := MvPowerSeries.pderiv_X_self
  have x11 : pd 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 1 := MvPowerSeries.pderiv_X_self
  have x01 : pd 0 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [MvPowerSeries.pderiv_X]
  have x10 : pd 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [MvPowerSeries.pderiv_X]
  rw [hW]
  simp only [pd, Derivation.leibniz, map_sub, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at x00 x11 x01 x10 e0 e1 p0 p1 ⊢
  rw [x00, x11, x01, x10]
  linear_combination (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * (-e0 + e1 + U * p0 - U * p1)
end Formalism.L2.Th1.B.Det
