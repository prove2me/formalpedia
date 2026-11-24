-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.euler_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:56.756936+00:00
-- url     : https://prove2.me/submissions/5c85ae1e-4385-401b-aa1a-55979ce726c4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.EulerComm := by
  intro r v w
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  refine LinearMap.ext fun f => ?_
  ext γ
  simp only [Module.End.mul_apply, hc]
  ring
end Formalism.FourierDecayAlt.P
