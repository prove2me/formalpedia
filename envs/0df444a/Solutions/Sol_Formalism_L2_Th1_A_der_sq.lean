-- Prove2me | solution 1 for Formalism.L2.Th1.A.der_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:20:27.684705+00:00
-- url     : https://prove2.me/submissions/a90a37f8-5153-4434-aa92-9a666b943b5e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Theorems.Thm_Formalism_L2_Th1_A_der_mul

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
variable {A : Type u} [CommRing A]
namespace Formalism.L2.Th1.A
theorem _root_.solution (d : Derivation ℤ A A) (a : A) : d (a ^ 2) = 2 * a * d a := by
  rw [pow_two, der_mul]
  ring
end Formalism.L2.Th1.A
