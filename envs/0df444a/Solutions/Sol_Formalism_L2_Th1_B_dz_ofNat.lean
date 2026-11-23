-- Prove2me | solution 1 for Formalism.L2.Th1.B.dz_ofNat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:04.698792+00:00
-- url     : https://prove2.me/submissions/70dd588f-6f89-4584-8f1d-52c5816afd50

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
theorem _root_.solution (n : ℕ) [n.AtLeastTwo] : dz (OfNat.ofNat n : PowerSeries K) = 0 := by
  rw [show (OfNat.ofNat n : PowerSeries K) = C (OfNat.ofNat n : K) from (map_ofNat C n).symm]
  exact PowerSeries.derivative_C
end Formalism.L2.Th1.B
