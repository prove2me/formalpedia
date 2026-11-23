-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.ev_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:22.849279+00:00
-- url     : https://prove2.me/submissions/72998bb2-a8ca-4fc0-a0d3-6ba6a16f7299

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_ev_apply

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
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6.PC
theorem _root_.solution (y : ℂ) (b : B) : ev y (C b) = b := by rw [ev_apply, Polynomial.eval₂_C]; rfl
end Formalism.FourierDecayAlt.P.Mx6.PC
