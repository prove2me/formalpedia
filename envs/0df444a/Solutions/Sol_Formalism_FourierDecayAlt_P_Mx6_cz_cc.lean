-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.cz_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:38.44512+00:00
-- url     : https://prove2.me/submissions/2b84e550-33be-4b1f-b0c0-ac37c756bfea

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_sc_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cc_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cz_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_mul


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
theorem _root_.solution : cz P * cc P = cc P * cz P := by
  rw [cc_sc, cz_sc, sc_mul, sc_mul]
  congr 1
  simp only [zP, zbP, ggiP]
  rw [Mx2.multiplierPair_mul, Mx2.multiplierPair_mul]
  exact Mx2.multiplierPair_comm _ _ _ _
end Formalism.FourierDecayAlt.P.Mx6
