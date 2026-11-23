-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.isPoly_kap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:15.153113+00:00
-- url     : https://prove2.me/submissions/3364cefb-b432-430c-bdf2-69f0bed348fe

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kap_sum

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
theorem _root_.solution {F : Ty P → ℂ → ℂ} (hF : ∀ π, IsPolyS (F π)) : IsPoly fun Y => kap P fun π => F π Y := by
  have : (fun Y => kap P fun π => F π Y) = fun Y => ∑ π, F π Y • kap P (Pi.single π 1) := by
    funext Y; exact kap_sum P _
  rw [this]
  exact IsPoly.sum _ fun π _ => IsPoly.smul (hF π) (IsPoly.const _)
end Formalism.FourierDecayAlt.P.Mx6.PC
