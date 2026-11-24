-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.DiffPh_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:58.337095+00:00
-- url     : https://prove2.me/submissions/7b3c863f-ca7e-4e5f-bc46-8c9cc03caa2d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_diff_eq

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
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution (hS : Sigma1Sq) (hL : SimeqLog) : DiffPh := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hCC
  have key := diff_eq (s2 := s2) hS hP he hF.2.2.1 hF.2.2.2.1 hCC.2.2.1
  refine ⟨key, fun hce => ?_⟩
  have hE1' : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
    simp [hCC.2.1]
  have hE1 : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := hE1'
  have hEI : Formalism.DworkPowerSeriesWeights.Integral (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2 : PowerSeries K) := by
    intro n
    rw [map_add, PowerSeries.C_apply, PowerSeries.X_apply, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_X_pow]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hCC.1 n) ?_)
    split_ifs
    · rw [mul_one]; exact hce
    · rw [mul_zero, norm_zero]; exact zero_le_one
  have hex := (hL K Unit (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) hE1 hEI).2
  have heq : (2 * Formalism.L2.Th1.B.phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P) l -
      2 * Formalism.L2.Th1.B.phO s2 P l : PowerSeries K) =
      -Formalism.L2.Th1.B.fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) - 0 := by
    linear_combination key
  unfold Formalism.InvariantFactorPaths.G7.Simeq at hex ⊢
  rw [heq]
  exact hex
end Formalism.L2.Th1.B.ParO
