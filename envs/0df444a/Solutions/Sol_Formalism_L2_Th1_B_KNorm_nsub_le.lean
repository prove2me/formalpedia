-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.nsub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:07.134879+00:00
-- url     : https://prove2.me/submissions/9a10483f-32ba-476e-b7a5-4147704f3e97

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_le
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
theorem _root_.solution {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a - b‖ ≤ r := by
  rw [sub_eq_add_neg]
  exact nadd_le ha (by rwa [norm_neg])
end Formalism.L2.Th1.B.KNorm
