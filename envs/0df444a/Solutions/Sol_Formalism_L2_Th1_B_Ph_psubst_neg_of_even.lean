-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.psubst_neg_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:30.436574+00:00
-- url     : https://prove2.me/submissions/fbf093a0-5d9a-4136-b006-2cebdf0ad434

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution {f l : PowerSeries K} (h : ∀ n, Odd n → coeff n f = 0)
    (hl : constantCoeff l = 0) : subst (-l) f = subst l f := by
  have hX : HasSubst ((-1 : K) • (X : PowerSeries K)) := HasSubst.smul_X' _
  have e1 : subst l ((-1 : K) • (X : PowerSeries K)) = -l := by
    rw [subst_smul (hs hl), subst_X (hs hl), neg_one_smul]
  have e2 : rescale (-1 : K) f = f := by
    ext n
    rw [coeff_rescale]
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, one_mul]
    · rw [h n ho, mul_zero]
  rw [← e1, ← subst_comp_subst_apply hX (hs hl), ← rescale_eq_subst, e2]
end Formalism.L2.Th1.B.Ph
