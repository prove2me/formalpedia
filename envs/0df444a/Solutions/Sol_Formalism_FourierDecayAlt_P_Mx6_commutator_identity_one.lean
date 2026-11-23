-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.commutator_identity_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:37.386316+00:00
-- url     : https://prove2.me/submissions/5481ddf7-dc3e-4fdb-9ddf-c726018d2271

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lca

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
theorem _root_.solution (N c g G X L L' : B) (α β : ℂ)
    (hNg : N * g = g * N + g * c) (hNX : N * X = X * N)
    (hgG : g * G = 1) (hGg : G * g = 1) (hcg : c * g = g * c)
    (hXg : X * g = g * X) (hXG : X * G = G * X) (hXc : X * c = c * X)
    (hLg : L * g = g * L) (hLg' : L' * g = g * L')
    (h1 : (α - β) • (X * L' - L' * X) = -(X * (L - L'))) :
    (α - β) • (g * X * (-N - β • c + G * L') - (-N - β • c + G * L') * (g * X)) =
      -(g * X * ((-N - α • c + G * L) - (-N - β • c + G * L'))) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNg, lca hNg, hNX, lc hNX, hgG, lc1 hgG, hGg, lc1 hGg, hcg, lc hcg,
    hXg, lc hXg, hXG, lc hXG, hXc, lc hXc, hLg, lc hLg, hLg', lc hLg'] at h1 ⊢
  linear_combination (norm := module) h1
end Formalism.FourierDecayAlt.P.Mx6
