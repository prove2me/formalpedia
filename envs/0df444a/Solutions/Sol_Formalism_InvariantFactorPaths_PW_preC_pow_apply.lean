-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.preC_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.755924+00:00
-- url     : https://prove2.me/submissions/1c16d2c8-3dd1-4639-88e5-9aa444b8e959

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds

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
variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (Y : Module.End K V) (j : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((preC (W := W) Y) ^ j) φ x = φ ((Y ^ j) x) := by
  induction j generalizing φ with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (preC (W := W) Y) j, pow_succ' Y j]
    exact ih (preC Y φ)
end Formalism.InvariantFactorPaths.PW
