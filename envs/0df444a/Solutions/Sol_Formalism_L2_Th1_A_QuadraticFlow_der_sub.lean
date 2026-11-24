-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.der_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:22.525088+00:00
-- url     : https://prove2.me/submissions/a41ad651-56df-4225-b7e1-c85b6b71c01a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_add
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_neg

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
theorem _root_.solution (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, der_add h, der_neg h, ← sub_eq_add_neg]
end Formalism.L2.Th1.A.QuadraticFlow
