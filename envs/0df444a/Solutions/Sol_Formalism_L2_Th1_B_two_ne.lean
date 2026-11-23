-- Prove2me | solution 1 for Formalism.L2.Th1.B.two_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:55.648267+00:00
-- url     : https://prove2.me/submissions/b1f32378-c088-41d9-b94c-c8e6c5a08f67

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
theorem _root_.solution : (2 : PowerSeries K) ≠ 0 := by
  intro h
  have h2 := congrArg (constantCoeff (R := K)) h
  rw [map_ofNat, map_zero] at h2
  exact two_ne_zero h2
end Formalism.L2.Th1.B
