-- Prove2me | solution 1 for Formalism.L2.Th1.A.der_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:13:15.752495+00:00
-- url     : https://prove2.me/submissions/3038a2c9-4291-4823-911a-09a7d09825af

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans

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
theorem _root_.solution (d : Derivation ℤ A A) (a : A) : d (3 * a) = 3 * d a := by
  rw [show (3 : A) * a = a + a + a by ring, map_add, map_add]
  ring
end Formalism.L2.Th1.A
