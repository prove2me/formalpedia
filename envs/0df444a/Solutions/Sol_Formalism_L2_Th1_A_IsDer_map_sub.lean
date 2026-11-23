-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.map_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:00.024808+00:00
-- url     : https://prove2.me/submissions/9ba33d0c-710b-496f-89b4-4539de8ec494

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg

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
theorem _root_.solution (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, h.map_add, h.map_neg, ← sub_eq_add_neg]
end Formalism.L2.Th1.A.IsDer
