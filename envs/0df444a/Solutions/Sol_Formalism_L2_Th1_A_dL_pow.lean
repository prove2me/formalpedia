-- Prove2me | solution 1 for Formalism.L2.Th1.A.dL_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:13:03.175801+00:00
-- url     : https://prove2.me/submissions/06d5a56e-3a2b-4bfa-8e3b-bcf624227764

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Theorems.Thm_Formalism_L2_Th1_A_dL_one
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution (f : LaurentSeries R) (n : ℕ) :
    dL (f ^ n) = (n : LaurentSeries R) * f ^ (n - 1) * dL f := by
  induction n with
  | zero => simp [dL_one]
  | succ k ih =>
    rw [pow_succ, dL_mul, ih]
    rcases k with _ | j
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring
end Formalism.L2.Th1.A
