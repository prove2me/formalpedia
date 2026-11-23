-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.ofEntries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:39.385833+00:00
-- url     : https://prove2.me/submissions/017df226-6b88-4ea7-a8bd-3268ed3f0411

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kronecker_E1_E2_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kronecker_embed_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_Pf_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_mul_Pf_apply

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.QQRTTOfEntries := by
  intro H P hP Y Y'
  apply Matrix.ext
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply, kronecker_E1_E2_apply, kronecker_embed_mul_apply,
    kronecker_embed_mul_apply]
  have h := H P hP Y' Y i j k l
  rw [smul_sub] at h
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact h
end Formalism.FourierDecayAlt.P.Mx6.PC
