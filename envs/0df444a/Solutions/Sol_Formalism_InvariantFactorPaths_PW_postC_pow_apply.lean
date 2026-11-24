-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.postC_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:24.341656+00:00
-- url     : https://prove2.me/submissions/6d6c73ed-f743-4079-8d49-4ab9da405042

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
theorem _root_.solution (X : Module.End K W) (i : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((postC X) ^ i) φ x = (X ^ i) (φ x) := by
  induction i generalizing φ with
  | zero => simp
  | succ i ih =>
    rw [pow_succ (postC (V := V) X) i, pow_succ X i]
    exact ih (postC X φ)
end Formalism.InvariantFactorPaths.PW
