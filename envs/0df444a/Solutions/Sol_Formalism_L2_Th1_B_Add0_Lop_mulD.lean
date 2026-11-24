-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.Lop_mulD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:20:25.506645+00:00
-- url     : https://prove2.me/submissions/917ccceb-ad08-4929-aa60-ec7cb28239f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pd_two

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
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution (N : A2) :
    Lop ((MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * N) =
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) ^ 2 * Lop N := by
  unfold Lop
  simp only [pd, Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), mul_one, mul_zero, zero_mul,
    add_zero, zero_add, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one, pow_zero, sub_zero, pd_two, map_zero]
  ring
end Formalism.L2.Th1.B.Add0
