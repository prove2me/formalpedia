-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.nf12
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:53.188922+00:00
-- url     : https://prove2.me/submissions/2e0d50dc-aa71-44b8-a8c5-de4193dbc309

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_operator_absorb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_Lamsx
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lams_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Gg__2bb78f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ns_g__feb0d2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cz_g
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mt_eq
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
theorem _root_.solution {u : ℂ} (hu : Good P u) : t12 P u = mt P u * t22 P u := by
  rw [t12, t22, mt_eq, raising_operator_absorb _ _ _ _ _ _ _ (Ns_g P) (x_Ns P u) (Gg P) (cz_g P) (kap_cz P _).symm (Lams_sc P _ _),
    L4.Lamsx P hu, raising_constant_eq_shift]
  congr 4
  ring
end Formalism.FourierDecayAlt.P.Mx6
