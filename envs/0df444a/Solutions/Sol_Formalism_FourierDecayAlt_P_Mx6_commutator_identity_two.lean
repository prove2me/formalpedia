-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.commutator_identity_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:37.81797+00:00
-- url     : https://prove2.me/submissions/f532ad16-184b-4d66-a9a8-c1142781650e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
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
theorem _root_.solution (N c G X L L' : B) (α β q : ℂ)
    (hNG : N * G = G * N - c * G) (hNX : N * X = X * N)
    (hGc : G * c = c * G)
    (hXG : X * G = G * X) (hXc : X * c = c * X)
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h1 : (α - β) • (X * L' - L' * X) = X * (L - L')) :
    (α - β) • (q • (G * X) * (-N - β • c + G * L') - (-N - β • c + G * L') * (q • (G * X))) =
      q • (G * X) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by
  have h1' := congrArg (fun x => q • (G * (G * x))) h1
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNG, lcs hNG, hNX, lc hNX, hGc, lc hGc,
    hXG, lc hXG, hXc, lc hXc, hLG, lc hLG, hLG', lc hLG'] at h1' ⊢
  linear_combination (norm := module) h1'
end Formalism.FourierDecayAlt.P.Mx6
