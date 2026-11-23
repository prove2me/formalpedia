-- Prove2me | solution 1 for Formalism.L2.Th1.A.der_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:00.09884+00:00
-- url     : https://prove2.me/submissions/462dd0cb-8177-4f48-bd4a-d597d1dc76f4

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
theorem _root_.solution (d : Derivation ℤ A A) (a b : A) : d (a * b) = a * d b + b * d a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
end Formalism.L2.Th1.A
