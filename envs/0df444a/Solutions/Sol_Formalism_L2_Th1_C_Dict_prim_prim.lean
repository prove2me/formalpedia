-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.prim_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:52.180025+00:00
-- url     : https://prove2.me/submissions/8d586f1f-3511-4227-9b51-4ead27c6317b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_B_Ph_coeff_prim_succ
import Theorems.Thm_Formalism_L2_Th1_B_Ph_coeff_zero_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Dict
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C.Dict
theorem _root_.solution (e : PowerSeries K) : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim e) = dblInt e := by
  ext n
  match n with
  | 0 => rw [Formalism.L2.Th1.B.Ph.coeff_zero_prim, dblInt, PowerSeries.coeff_mk, if_pos (by norm_num)]
  | 1 =>
    rw [Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_zero_prim, zero_div, dblInt,
      PowerSeries.coeff_mk, if_pos (by norm_num)]
  | m + 2 =>
    rw [Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_prim_succ, dblInt,
      PowerSeries.coeff_mk, if_neg (by omega), Nat.add_sub_cancel, div_div]
    congr 1
    push_cast
    ring
end Formalism.L2.Th1.C.Dict
