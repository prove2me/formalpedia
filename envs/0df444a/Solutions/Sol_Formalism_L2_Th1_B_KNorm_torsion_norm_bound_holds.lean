-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.torsion_norm_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:43.238796+00:00
-- url     : https://prove2.me/submissions/343fa515-6df9-44bf-a87a-871b7cb40cf5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_tors_bound

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
open Classical
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution : TorsBound := by
  intro K _ _ W hW h2 P k hk hP
  exact tors_bound hW h2 P k hk hP
end Formalism.L2.Th1.B.KNorm
