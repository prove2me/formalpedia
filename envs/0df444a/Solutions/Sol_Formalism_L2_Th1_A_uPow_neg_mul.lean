-- Prove2me | solution 1 for Formalism.L2.Th1.A.uPow_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.014031+00:00
-- url     : https://prove2.me/submissions/d78b40e5-7781-43fc-8017-96a9b1f66eaf

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
theorem _root_.solution (n : ℤ) : (uPow (-n) : LaurentSeries R) * uPow n = 1 := by
  rw [← uPow_add]
  first | rw [neg_add_cancel] | rw [neg_add_self] | rw [add_left_neg]
  exact uPow_zero
end Formalism.L2.Th1.A
