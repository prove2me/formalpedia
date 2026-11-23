-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.mul_Pf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:42.159799+00:00
-- url     : https://prove2.me/submissions/144af6ac-93ad-4dab-85f2-f9597f4a520e

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
theorem _root_.solution (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) := by
  fin_cases j <;> fin_cases l <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]
end Formalism.FourierDecayAlt.P.Mx6.PC
