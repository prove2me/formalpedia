-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:47.008926+00:00
-- url     : https://prove2.me/submissions/43bcb906-dbd9-4591-b4ac-4a7506ce5370

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul

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
theorem _root_.solution (h : IsDer D) : IsDer (fun a => -D a) :=
  ⟨fun a b => by
    show -D (a + b) = -D a + -D b
    rw [h.map_add]
    ring,
   fun a b => by
    show -D (a * b) = a * -D b + b * -D a
    rw [h.map_mul]
    ring⟩
end Formalism.L2.Th1.A.IsDer
