-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sq.even_iff_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:17.988862+00:00
-- url     : https://prove2.me/submissions/0706088d-db9f-4b38-a4a5-f803653843a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Sq
theorem _root_.solution (f : PowerSeries K) :
    (∀ n, Odd n → coeff n f = 0) ↔ rescale (-1 : K) f = f := by
  constructor
  · intro h
    ext n
    rw [PowerSeries.coeff_rescale]
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, one_mul]
    · rw [h n ho, mul_zero]
  · intro h n hn
    have h1 := congrArg (coeff n) h
    rw [PowerSeries.coeff_rescale, hn.neg_one_pow] at h1
    have h2 : (2 : K) * coeff n f = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
end Formalism.L2.Th1.B.Sq
