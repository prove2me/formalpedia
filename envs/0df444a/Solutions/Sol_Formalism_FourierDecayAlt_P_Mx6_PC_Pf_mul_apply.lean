-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.Pf_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:22.36649+00:00
-- url     : https://prove2.me/submissions/87549de0-75d5-486a-8660-2aa4accdb1a5

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable (P : Par)
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Mx6.PC
theorem _root_.solution (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]
end Formalism.FourierDecayAlt.P.Mx6.PC
