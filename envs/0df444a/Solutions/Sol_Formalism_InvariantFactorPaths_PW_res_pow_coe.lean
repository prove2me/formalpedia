-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.res_pow_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.932403+00:00
-- url     : https://prove2.me/submissions/77a4a084-48d8-45b0-91d1-55436deb79f4

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_res_E_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (k : ℕ) (x : U) :
    ((((res G U hU).E a b ^ k) x : U) : V) = (G.E a b ^ k) (x : V) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    show (((res G U hU).E a b (((res G U hU).E a b ^ k) x) : U) : V) = G.E a b ((G.E a b ^ k) (x : V))
    rw [res_E_coe, ih]
end Formalism.InvariantFactorPaths.PW
