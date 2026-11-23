-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.isPoly_QQr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:46.310618+00:00
-- url     : https://prove2.me/submissions/b16f671d-890d-469c-945b-17f76fc21f71

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_diagonal_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_t21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_upper_right_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_upper_left_entry

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
namespace Formalism.FourierDecayAlt.P.Mx6.PC
theorem _root_.solution (i j : Fin 2) : IsPoly fun Y => QQr P Y i j := by
  fin_cases i <;> fin_cases j
  · exact isPoly_upper_left_entry P
  · exact isPoly_upper_right_entry P
  · exact isPoly_t21 P
  · exact isPoly_diagonal_entry P
end Formalism.FourierDecayAlt.P.Mx6.PC
