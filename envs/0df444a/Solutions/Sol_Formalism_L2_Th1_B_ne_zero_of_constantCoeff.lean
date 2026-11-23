-- Prove2me | solution 1 for Formalism.L2.Th1.B.ne_zero_of_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:37.286799+00:00
-- url     : https://prove2.me/submissions/cc68fcfe-3d77-4cab-8c25-ebc3bf0dea24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution {f : PowerSeries K} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (map_zero _)
end Formalism.L2.Th1.B
