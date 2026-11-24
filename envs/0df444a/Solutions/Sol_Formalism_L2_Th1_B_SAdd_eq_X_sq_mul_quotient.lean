-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.eq_X_sq_mul_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:07.07075+00:00
-- url     : https://prove2.me/submissions/5bf70739-fde8-4e2f-a676-3295e0a881e3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq

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
theorem _root_.solution {w : PowerSeries K} (h0 : constantCoeff w = 0) (h1 : coeff 1 w = 0) :
    w = X ^ 2 * divByXSq w := by
  ext n
  rw [coeff_X_pow_mul']
  by_cases h : 2 ≤ n
  · rw [if_pos h, divByXSq, coeff_mk, Nat.sub_add_cancel h]
  · rw [if_neg h]
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · rw [coeff_zero_eq_constantCoeff_apply, h0]
    · exact h1
end Formalism.L2.Th1.B.SAdd
