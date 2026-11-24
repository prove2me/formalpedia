-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.der_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:20.542476+00:00
-- url     : https://prove2.me/submissions/039c40d8-9c9b-411e-8c80-7161977a7bf2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_mul

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
open Formalism.L2.Th1.A.QuadraticFlow
variable {A : Type u} [CommRing A] {D : A → A}
namespace Formalism.L2.Th1.A.QuadraticFlow
theorem _root_.solution (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [sq, der_mul h]
  ring
end Formalism.L2.Th1.A.QuadraticFlow
