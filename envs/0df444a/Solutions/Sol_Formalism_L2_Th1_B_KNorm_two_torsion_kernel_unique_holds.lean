-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.two_torsion_kernel_unique_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:41.344721+00:00
-- url     : https://prove2.me/submissions/ee3eb719-bf92-4f1b-b408-e93c9a27c540

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_two_torsion_kernel_norm_unique

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
theorem _root_.solution : TwoTorsionKernelUnique := by
  intro K _ _ W hW h2 ha P Q hP0 hP hPE
  exact two_torsion_kernel_norm_unique hW h2 ha P Q hP0 hP hPE
end Formalism.L2.Th1.B.KNorm
