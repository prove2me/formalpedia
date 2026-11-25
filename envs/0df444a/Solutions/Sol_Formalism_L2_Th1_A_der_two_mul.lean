-- Prove2me | solution 1 for Formalism.L2.Th1.A.der_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:13:19.623856+00:00
-- url     : https://prove2.me/submissions/2ab5a771-1f9c-4a0b-9267-1c7f6cb05a27

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
theorem _root_.solution (d : Derivation ℤ A A) (a : A) : d (2 * a) = 2 * d a := by
  rw [two_mul, map_add, two_mul]
end Formalism.L2.Th1.A
