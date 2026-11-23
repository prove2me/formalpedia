-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.ev_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:04.662652+00:00
-- url     : https://prove2.me/submissions/071893b9-81d8-4f50-be65-59c46eb8aff7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ev_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
variable {B : Type} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (Y : ℂ) (p : B[X]) : ev Y p = ∑ i ∈ p.support, Y ^ i • p.coeff i := by
  rw [ev_apply, eval₂_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]
end Formalism.FourierDecayAlt.P.Mx7
