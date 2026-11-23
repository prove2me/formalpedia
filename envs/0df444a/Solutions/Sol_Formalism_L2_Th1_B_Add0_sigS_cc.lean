-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.sigS_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:11.000909+00:00
-- url     : https://prove2.me/submissions/a44b1439-0aaa-4f34-b39b-01f36f589f73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference

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
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  simp only [sigS, map_neg, neg_eq_zero]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, prim, PowerSeries.coeff_mk, if_pos rfl]
end Formalism.L2.Th1.B.Add0
