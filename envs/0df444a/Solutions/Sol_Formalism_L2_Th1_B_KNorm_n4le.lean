-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.n4le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:49.823527+00:00
-- url     : https://prove2.me/submissions/e14f366d-d7d6-470e-aed4-6a41f23918f3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nmul1
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_n2le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution : ‖(4 : K)‖ ≤ 1 := by
  rw [show (4 : K) = 2 * 2 by norm_num]
  exact nmul1 n2le n2le
end Formalism.L2.Th1.B.KNorm
