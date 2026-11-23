-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.smul_GG_sq_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:25.596247+00:00
-- url     : https://prove2.me/submissions/006942cf-b58f-4504-8672-8628949ea8bd

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc1

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
theorem _root_.solution (g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1) :
    t • (G * G) = z * (w * (G * G)) - G := by
  have h : algebraMap ℂ B t = z * w - g := by rw [hg]; abel
  rw [Algebra.smul_def, h]
  simp only [sub_mul, mul_assoc, lc1 hgG]
end Formalism.FourierDecayAlt.P.Mx6
