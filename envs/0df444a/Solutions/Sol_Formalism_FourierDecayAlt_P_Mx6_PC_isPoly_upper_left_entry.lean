-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.isPoly_upper_left_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:00.710544+00:00
-- url     : https://prove2.me/submissions/515f14e8-d84c-49c1-89c3-3c5789b4a5f6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPolyS_wC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_xA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_l0A
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_m0A
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_S21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_S12
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_quartic_sum

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
theorem _root_.solution : IsPoly fun Y => t11 P Y :=
  (((((IsPoly.const _).mul (isPoly_kap P (isPolyS_wC P))).add
    ((((IsPoly.const _).mul (isPoly_xA P)).mul (isPoly_m0A P)).mul (isPoly_l0A P))).add
    ((((IsPoly.const _).mul (isPoly_m0A P)).mul (IsPoly.const _)).mul (isPoly_S21 P))).add
    ((isPoly_S12 P).mul (isPoly_l0A P))).add ((IsPoly.const _).mul (isPoly_quartic_sum P))
end Formalism.FourierDecayAlt.P.Mx6.PC
