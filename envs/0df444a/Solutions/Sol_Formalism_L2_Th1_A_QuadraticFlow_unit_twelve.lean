-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.unit_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:54.599683+00:00
-- url     : https://prove2.me/submissions/eb0edc6a-4c2a-48d0-975c-f487c8d4f182

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo

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
theorem _root_.solution (h6 : IsUnit (6 : A)) : IsUnit (12 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left (e6 ▸ h6)
  have e12 : (12 : A) = 6 * 2 := by norm_num
  rw [e12]
  exact h6.mul h2
end Formalism.L2.Th1.A.QuadraticFlow
