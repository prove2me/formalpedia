-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.block_frame_conjugation_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:19.289773+00:00
-- url     : https://prove2.me/submissions/7e8c135d-7de1-402f-808d-038f2d93e96e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] (g gi z N : R) (a e : ℂ) (h1 : g * gi = 1)
    (hN : N * g = g * N - e • z) (hzg : Commute z g) (hzgi : Commute z gi) :
    g * (-N - a • (z * gi)) * gi = -N - (a + e) • (gi * z) := by
  have hgN : g * N = N * g + e • z := by rw [hN]; abel
  have e1 : g * N * gi = N + e • (z * gi) := by
    rw [hgN, add_mul, mul_assoc, h1, mul_one, smul_mul_assoc]
  have e2 : g * (z * gi) * gi = z * gi := by
    rw [← mul_assoc, ← hzg.eq, mul_assoc z g gi, h1, mul_one]
  calc g * (-N - a • (z * gi)) * gi = -(g * N * gi) - a • (g * (z * gi) * gi) := by
        rw [mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
    _ = -N - (a + e) • (gi * z) := by
        rw [e1, e2, ← hzgi.eq, add_smul]
        abel
end Formalism.FourierDecayAlt.P.Mx5
