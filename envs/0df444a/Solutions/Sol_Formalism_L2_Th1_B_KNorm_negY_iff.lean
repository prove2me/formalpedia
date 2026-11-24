-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.negY_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:06.753062+00:00
-- url     : https://prove2.me/submissions/5ace1291-9f94-4ab7-8181-74707170d046

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds

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
variable {K : Type} [Field K] {W : WeierstrassCurve K} {x y : K}
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [WeierstrassCurve.Affine.negY]
  constructor <;> intro h <;> linear_combination h
end Formalism.L2.Th1.B.KNorm
