-- Prove2me | solution 1 for Formalism.L2.Th1.B.dz_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:35.700899+00:00
-- url     : https://prove2.me/submissions/be24c4ab-2505-4f8c-9eff-7b5ea21a0655

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Theorems.Thm_Formalism_L2_Th1_B_dz_mul
import Theorems.Thm_Formalism_L2_Th1_B_dz_sq

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
theorem _root_.solution (f : PowerSeries K) : dz (f ^ 3) = 3 * f ^ 2 * dz f := by
  rw [pow_succ, dz_mul, dz_sq]
  ring
end Formalism.L2.Th1.B
