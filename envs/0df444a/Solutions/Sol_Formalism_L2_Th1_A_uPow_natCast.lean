-- Prove2me | solution 1 for Formalism.L2.Th1.A.uPow_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:20:19.172029+00:00
-- url     : https://prove2.me/submissions/b0062654-ff07-421d-9dd7-4f5aae9e4dd1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Theorems.Thm_Formalism_L2_Th1_A_uPow_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution (n : ℕ) : (uPow (n : ℤ) : LaurentSeries R) = toL (X ^ n) := by
  induction n with
  | zero => simp [uPow_zero]
  | succ k ih => rw [Nat.cast_succ, uPow_add, ih, uPow_one, ← map_mul, pow_succ]
end Formalism.L2.Th1.A
