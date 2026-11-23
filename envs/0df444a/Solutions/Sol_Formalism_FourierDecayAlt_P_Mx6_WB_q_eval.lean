-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.q_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:53.159776+00:00
-- url     : https://prove2.me/submissions/a70707b6-e747-4d7d-ac3e-5cfef96ebaf2

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
theorem _root_.solution (P : Par) (u : ℂ) : (C (-((P.T : ℂ) * P.T')) * q1P P).eval u = qC P u := by
  unfold q1P qC
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)
end Formalism.FourierDecayAlt.P.Mx6.WB
