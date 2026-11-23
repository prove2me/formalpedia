-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.coordinate_commute_raising_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:38.311776+00:00
-- url     : https://prove2.me/submissions/bf9c627e-1f29-4975-93f1-b30754af3c45

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_x_Ns
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_cz

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
theorem _root_.solution (u v : ℂ) : xA P u * m0A P v = m0A P v * xA P u := by
  rw [raising_constant_eq_shift]
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, x_Ns]
  rw [xA, kap_cz]
end Formalism.FourierDecayAlt.P.Mx6
