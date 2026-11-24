-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.homAct_precomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:17.269383+00:00
-- url     : https://prove2.me/submissions/b8b51ca0-6c21-4568-9ac0-fe4384439af9

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_apply

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
theorem _root_.solution {V' : Type} [AddCommGroup V'] [Module K V'] (EV : ι → ι → Module.End K V)
    (EV' : ι → ι → Module.End K V') (EW : ι → ι → Module.End K W) (ι' : V' →ₗ[K] V)
    (hι : ∀ a b x, ι' (EV' a b x) = EV a b (ι' x)) (a b : ι) (φ : V →ₗ[K] W) :
    (homAct EV EW a b φ) ∘ₗ ι' = homAct EV' EW a b (φ ∘ₗ ι') := by
  ext x
  simp [homAct_apply, hι]
end Formalism.InvariantFactorPaths.PW
