-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.raising_operator_absorb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:41.792843+00:00
-- url     : https://prove2.me/submissions/ad3a43ef-cab9-4d0c-b3ac-c75c003101ad

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lcs

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
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (Ns cz g G X Ls : B) (α : ℂ)
    (hNsg : Ns * g = g * Ns - g * cz) (hNsX : Ns * X = X * Ns) (hGg : G * g = 1) (hczg : cz * g = g * cz)
    (hczX : cz * X = X * cz) (hLsg : Ls * g = g * Ls) :
    (-Ns - α • cz + G * Ls) * (g * X) = g * X * (-Ns - (α - 1) • cz) + Ls * X := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNsg, lcs hNsg, hNsX, hGg, lc1 hGg, hczg, lc hczg, hczX, hLsg, lc hLsg]
  module
end Formalism.FourierDecayAlt.P.Mx6
