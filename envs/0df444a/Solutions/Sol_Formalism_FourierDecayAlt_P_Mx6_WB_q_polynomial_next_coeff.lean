-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.q_polynomial_next_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:42.236305+00:00
-- url     : https://prove2.me/submissions/3002bbc5-068b-4b66-96df-dab551809c17

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) :
    (q1P P).nextCoeff = ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) := by
  unfold q1P
  rw [Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(monic_X_add_C _).nextCoeff_mul (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]
end Formalism.FourierDecayAlt.P.Mx6.WB
