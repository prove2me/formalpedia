-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.prim_prim_even
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:26.464527+00:00
-- url     : https://prove2.me/submissions/ea88aec6-f6df-436f-9333-ac858a8c1684

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution {f : PowerSeries K} (h : ∀ n, Odd n → coeff n f = 0) :
    ∀ n, Odd n → coeff n (prim (prim f)) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := hn
  rw [coeff_prim_succ]
  rcases k with _ | k
  · simp [coeff_zero_prim]
  · have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e, coeff_prim_succ, h (2 * k + 1) (odd_two_mul_add_one k)]
    simp
end Formalism.L2.Th1.B.Ph
