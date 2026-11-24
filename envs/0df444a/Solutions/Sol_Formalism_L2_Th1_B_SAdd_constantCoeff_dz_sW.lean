-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.constantCoeff_dz_sW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:57.322745+00:00
-- url     : https://prove2.me/submissions/67670d3c-2768-4b04-be94-efdbee07755d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_coeff_one_sW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution {w : PowerSeries K} (h2 : coeff 2 w = 1) :
    constantCoeff (dz (sW w)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, dz, coeff_derivative, zero_add, coeff_one_sW h2]
  simp
end Formalism.L2.Th1.B.SAdd
