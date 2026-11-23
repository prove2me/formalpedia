-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.commutator_t22_m
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:02.880434+00:00
-- url     : https://prove2.me/submissions/570db7be-b619-4ea3-9dbd-4575facc9928

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_relation_diagonal_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_t22
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_lA

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
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P u * mt P v - mt P v * t22 P u) = (mt P u - mt P v) * t22 P u := by
  have h := congrArg star (lowering_relation_diagonal_left P (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_t22, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h
end Formalism.FourierDecayAlt.P.Mx6
