-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.map_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:11.961188+00:00
-- url     : https://prove2.me/submissions/2707dc6c-cea8-4692-ac85-33c0f8cd8418

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.IsDer
variable {A : Type u} [CommRing A] {D : A → A}
namespace Formalism.L2.Th1.A.IsDer
theorem _root_.solution (h : IsDer D) (a : A) (n : ℕ) : D (a ^ n) = (n : A) * a ^ (n - 1) * D a := by
  rcases n with _ | n
  · rw [pow_zero, h.map_one, Nat.cast_zero, zero_mul, zero_mul]
  · rw [h.map_pow_succ, Nat.add_sub_cancel]
    push_cast
    ring
end Formalism.L2.Th1.A.IsDer
