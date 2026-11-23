-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.raising_pair_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:41.846148+00:00
-- url     : https://prove2.me/submissions/ff622a34-9c6a-4630-9e7c-5f88b9fd312f

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
theorem _root_.solution (N c G L L' : B) (α β : ℂ)
    (hNc : N * c = c * N - c * c) (hNG : N * G = G * N - c * G)
    (hNL : N * L = L * N - c * L) (hNL' : N * L' = L' * N - c * L')
    (hGc : G * c = c * G) (hLc : L * c = c * L) (hLc' : L' * c = c * L')
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h3 : (α - β) • (L * L' - L' * L) = (L - L') * (L - L')) :
    (α - β) • ((-N - α • c + G * L) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-N - α • c + G * L)) =
      ((-N - α • c + G * L) - (-N - β • c + G * L')) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by
  have h3' := congrArg (fun x => G * (G * x)) h3
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNc, lcs hNc, hNG, lcs hNG, hNL, hNL', hGc, lc hGc, hLc, lc hLc,
    hLc', lc hLc', hLG, lc hLG, hLG', lc hLG'] at h3' ⊢
  linear_combination (norm := module) h3'
end Formalism.FourierDecayAlt.P.Mx6
