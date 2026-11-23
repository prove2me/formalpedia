-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.xC_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:32.301214+00:00
-- url     : https://prove2.me/submissions/8fbd0df2-ed9d-4572-93a2-b38029a3bdad

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

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
theorem _root_.solution (π : Ty P) (u : ℂ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    xC P π u = (u + (rho P π j : ℂ)) * xEx P {j} π u := by
  rw [xC, xEx, Finset.sdiff_singleton_eq_erase]
  exact (Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) hj).symm
end Formalism.FourierDecayAlt.P.Mx6
