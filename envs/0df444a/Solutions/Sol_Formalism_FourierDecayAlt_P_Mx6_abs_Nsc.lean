-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.abs_Nsc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:36.144886+00:00
-- url     : https://prove2.me/submissions/e0cfcf12-d6a7-4d9f-b69a-574b7770d09f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_smul_GG_sq_identity

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
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (Ns g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1)
    (hNsw : Ns * w = w * Ns - 1) (hNsG : Ns * G = G * Ns + z * G * G) (hwz : w * z = z * w) :
    Ns * (w * G) = (w * G) * Ns + t • (G * G) := by
  rw [smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNsw]
  simp only [sub_mul, mul_assoc, hNsG, mul_add, one_mul, lc hwz]
  abel
end Formalism.FourierDecayAlt.P.Mx6
