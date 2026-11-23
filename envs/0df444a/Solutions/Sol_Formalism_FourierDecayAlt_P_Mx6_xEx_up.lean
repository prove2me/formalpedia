-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.xEx_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:20.400144+00:00
-- url     : https://prove2.me/submissions/b3bdc3f9-46ea-4b74-91c3-a8fbebbd8008

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_rho_up

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution {j : ℕ} {π π' : Ty P} (h : Up P j π π') (ex : Finset ℕ) (hj : j ∈ ex) (u : ℂ) :
    xEx P ex π' u = xEx P ex π u := by
  unfold xEx
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_sdiff.1 hi
  have hne : i ≠ j := fun e => hi'.2 (e ▸ hj)
  rw [rho_up P h hi'.1, if_neg hne, add_zero]
end Formalism.FourierDecayAlt.P.Mx6
