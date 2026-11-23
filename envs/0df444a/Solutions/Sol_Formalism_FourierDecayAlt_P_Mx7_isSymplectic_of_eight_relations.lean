-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.isSymplectic_of_eight_relations
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:21.133886+00:00
-- url     : https://prove2.me/submissions/7f159af9-3b6a-492a-9724-0cd5d65e5d95

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_ext

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
open Matrix
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (a b c d a' b' c' d' q : B)
    (e1 : a' * c - c' * a = 0) (e2 : a' * d - c' * b = q) (e3 : b' * c - d' * a = -q) (e4 : b' * d - d' * b = 0)
    (e5 : a * b' - b * a' = 0) (e6 : a * d' - b * c' = q) (e7 : c * b' - d * a' = -q) (e8 : c * d' - d * c' = 0) :
    (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ * Formalism.YangianSpanCharacter.T.J B * !![a, b; c, d] = q • Formalism.YangianSpanCharacter.T.J B ∧
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * Formalism.YangianSpanCharacter.T.J B * (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ = q • Formalism.YangianSpanCharacter.T.J B := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (norm := noncomm_ring) e1
    · linear_combination (norm := noncomm_ring) e2
    · linear_combination (norm := noncomm_ring) e3
    · linear_combination (norm := noncomm_ring) e4
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (norm := noncomm_ring) e5
    · linear_combination (norm := noncomm_ring) e6
    · linear_combination (norm := noncomm_ring) e7
    · linear_combination (norm := noncomm_ring) e8
end Formalism.FourierDecayAlt.P.Mx7
