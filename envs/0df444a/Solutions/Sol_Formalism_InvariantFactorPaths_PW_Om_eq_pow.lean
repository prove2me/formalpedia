-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:39.893065+00:00
-- url     : https://prove2.me/submissions/6cf3d5f4-4f33-44af-b515-460b7fe23060

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lop_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) (q : ℕ) :
    Om E S z q = ((∑ i ∈ S, lop (E z i) (E i z)) ^ q) 1 := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih, LinearMap.sum_apply]
    simp only [lop_apply]
    rfl
end Formalism.InvariantFactorPaths.PW
