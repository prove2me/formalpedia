-- Prove2me | solution 1 for Formalism.L2.Th1.A.dL_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:26:58.09397+00:00
-- url     : https://prove2.me/submissions/ccbade44-913f-46c4-9535-e909228eab41

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent

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
theorem _root_.solution (r : R) (f : LaurentSeries R) :
    dL (HahnSeries.C r * f) = HahnSeries.C r * dL f := by
  rw [dL_mul, dL_C, mul_zero, add_zero]
end Formalism.L2.Th1.A
