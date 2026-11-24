-- Prove2me | solution 1 for Formalism.L2.Th1.B.mul_pd_fLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:10.771571+00:00
-- url     : https://prove2.me/submissions/9c8a3dfe-a29b-4ae7-8745-1d0c61f7de2b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_one_add_mul_deriv_log_subst
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution [Finite ι] (i : ι) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) : g * pd i (fLog g) = pd i g := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hD := Formalism.G.LogCR.pderiv_psubst hg1 (log K) i
  have hL := one_add_mul_deriv_log_subst (HasSubst.of_constantCoeff_zero hg1)
  have e : (1 : MvPowerSeries ι K) + (g - 1) = g := by ring
  rw [e] at hL
  unfold fLog
  show g * MvPowerSeries.pderiv K i (PowerSeries.subst (g - 1) (log K)) = MvPowerSeries.pderiv K i g
  rw [hD, ← mul_assoc, hL, one_mul, map_sub, Derivation.map_one_eq_zero, sub_zero]
end Formalism.L2.Th1.B
