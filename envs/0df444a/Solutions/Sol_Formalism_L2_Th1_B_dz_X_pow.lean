-- Prove2me | solution 1 for Formalism.L2.Th1.B.dz_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:44.270799+00:00
-- url     : https://prove2.me/submissions/9efc8801-615f-49c8-a263-5ee53f25ccdb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Theorems.Thm_Formalism_L2_Th1_B_dz_X
import Theorems.Thm_Formalism_L2_Th1_B_dz_mul

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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution (n : ℕ) : dz ((X : PowerSeries K) ^ (n + 1)) = ((n : PowerSeries K) + 1) * X ^ n := by
  induction n with
  | zero => simp [dz_X]
  | succ n ih =>
    rw [pow_succ, dz_mul, ih, dz_X]
    push_cast
    ring
end Formalism.L2.Th1.B
