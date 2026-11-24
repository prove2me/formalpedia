-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.px_add_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:10.160733+00:00
-- url     : https://prove2.me/submissions/1e688916-0a57-4f85-8f5a-8a1587e93f48

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
variable [DecidableEq K]
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) :
    px W (Point.some x y h + Point.some x y h)
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  rw [WeierstrassCurve.Affine.Point.add_some (fun hxy => hy hxy.2)]
  rfl
end Formalism.L2.Th1.B.KNorm
