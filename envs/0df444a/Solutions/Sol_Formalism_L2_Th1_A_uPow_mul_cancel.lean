-- Prove2me | solution 1 for Formalism.L2.Th1.A.uPow_mul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:20:18.044309+00:00
-- url     : https://prove2.me/submissions/a21bb1b1-f13c-48a4-b160-49bdf059926c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Theorems.Thm_Formalism_L2_Th1_A_uPow_neg_mul

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
theorem _root_.solution (n : ℤ) {f g : LaurentSeries R} (h : uPow n * f = uPow n * g) :
    f = g := by
  calc f = uPow (-n) * (uPow n * f) := by rw [← mul_assoc, uPow_neg_mul, one_mul]
    _ = uPow (-n) * (uPow n * g) := by rw [h]
    _ = g := by rw [← mul_assoc, uPow_neg_mul, one_mul]
end Formalism.L2.Th1.A
