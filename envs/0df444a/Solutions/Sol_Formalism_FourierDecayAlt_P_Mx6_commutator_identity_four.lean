-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.commutator_identity_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:37.151695+00:00
-- url     : https://prove2.me/submissions/b73d0bba-c056-4787-83c9-90b5ef827c39

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lcs
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
theorem _root_.solution (N Ns c cz G K Ls L' : B) (α β t : ℂ)
    (hcurv : Ns * N = N * Ns + K * (G * G))
    (hNsc : Ns * c = c * Ns + t • (G * G)) (hNcz : N * cz = cz * N - t • (G * G))
    (hNG : N * G = G * N - c * G) (hNsG : Ns * G = G * Ns + cz * G)
    (hNsL' : Ns * L' = L' * Ns - cz * L') (hNLs : N * Ls = Ls * N + c * Ls)
    (hGc : G * c = c * G) (hGcz : G * cz = cz * G) (hczc : cz * c = c * cz)
    (hLc' : L' * c = c * L') (hLcz' : L' * cz = cz * L') (hLG' : L' * G = G * L')
    (hLsc : Ls * c = c * Ls) (hLscz : Ls * cz = cz * Ls) (hLsG : Ls * G = G * Ls) :
    (-Ns - α • cz + G * Ls) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-Ns - α • cz + G * Ls) =
      K * (G * G) + ((α + β) * t) • (G * G) + G * (G * (Ls * L' - L' * Ls)) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hcurv, hNsc, hNcz, hNG, lcs hNG, hNsG, lca hNsG, hNsL', hNLs,
    hGc, lc hGc, hGcz, lc hGcz, hczc, lc hczc, hLc', lc hLc', hLcz', lc hLcz', hLG', lc hLG',
    hLsc, lc hLsc, hLscz, lc hLscz, hLsG, lc hLsG]
  module
end Formalism.FourierDecayAlt.P.Mx6
