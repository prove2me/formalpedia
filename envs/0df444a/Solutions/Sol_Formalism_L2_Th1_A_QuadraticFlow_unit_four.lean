-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.unit_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:23.886143+00:00
-- url     : https://prove2.me/submissions/8465597d-9924-43f1-a761-90eb3aeff122

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
theorem _root_.solution (h6 : IsUnit (6 : A)) : IsUnit (4 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  rw [e6] at h6
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left h6
  have e4 : (4 : A) = 2 * 2 := by norm_num
  rw [e4]
  exact h2.mul h2
end Formalism.L2.Th1.A.QuadraticFlow
