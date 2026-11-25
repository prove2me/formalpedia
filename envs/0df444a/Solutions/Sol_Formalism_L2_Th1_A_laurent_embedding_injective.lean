-- Prove2me | solution 1 for Formalism.L2.Th1.A.laurent_embedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:33:29.567043+00:00
-- url     : https://prove2.me/submissions/d24726ed-7d52-4eb5-9be2-bb85592548f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Theorems.Thm_Formalism_L2_Th1_A_uPow_mul_cancel
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution : ToLInjective.{u} := by
  intro R _
  exact ⟨toL_injective, fun n f g h => uPow_mul_cancel n h⟩
end Formalism.L2.Th1.A
