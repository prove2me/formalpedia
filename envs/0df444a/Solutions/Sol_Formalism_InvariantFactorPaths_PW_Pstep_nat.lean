-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:33.731796+00:00
-- url     : https://prove2.me/submissions/03ab1eb5-652b-4236-825e-8c0ff343db93

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_nat

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
    (h : ∀ a b x, θ (E a b x) = E' a b (θ x)) (S : Finset ι) (z : ι) (l : ℕ) (x : W) :
    θ (Pstep E S z l x) = Pstep E' S z l (θ x) := by
  simp only [Pstep, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Om_nat E E' θ h]
end Formalism.InvariantFactorPaths.PW
