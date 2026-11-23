-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.map_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:41.672527+00:00
-- url     : https://prove2.me/submissions/4efa010e-d2fc-4b9b-bfeb-c7a05998f51d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic

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
theorem _root_.solution (h : IsDer D) (a : A) : D (-a) = -D a := by
  have h1 := h.1 a (-a)
  rw [show a + -a = 0 by ring, h.map_zero] at h1
  linear_combination -h1
end Formalism.L2.Th1.A.IsDer
