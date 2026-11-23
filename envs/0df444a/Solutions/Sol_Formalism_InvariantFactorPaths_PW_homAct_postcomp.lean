-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.homAct_postcomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:01.903429+00:00
-- url     : https://prove2.me/submissions/329583e5-1554-416e-82fd-bcc07f4978a9

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
theorem _root_.solution {W' : Type} [AddCommGroup W'] [Module K W'] (EV : ι → ι → Module.End K V)
    (EW : ι → ι → Module.End K W) (EW' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (hθ : ∀ a b x, θ (EW a b x) = EW' a b (θ x)) (a b : ι) (φ : V →ₗ[K] W) :
    θ ∘ₗ (homAct EV EW a b φ) = homAct EV EW' a b (θ ∘ₗ φ) := by
  ext x
  simp [homAct_apply, hθ]
end Formalism.InvariantFactorPaths.PW
