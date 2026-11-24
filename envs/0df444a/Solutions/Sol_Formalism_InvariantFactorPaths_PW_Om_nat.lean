-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:40.192024+00:00
-- url     : https://prove2.me/submissions/1a424cda-3111-42c6-ac38-29aead04b93f

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv

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
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (E : ι → ι → Module.End K W) (E' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (h : ∀ a b x, θ (E a b x) = E' a b (θ x)) (S : Finset ι) (z : ι) (q : ℕ) :
    ∀ x, θ (Om E S z q x) = Om E' S z q (θ x) := by
  induction q with
  | zero => intro x; simp [Om]
  | succ q ih =>
    intro x
    simp only [Om, LinearMap.sum_apply, map_sum, Module.End.mul_apply, ih, h]
end Formalism.InvariantFactorPaths.PW
