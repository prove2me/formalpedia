-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.raising_relation_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:24.487347+00:00
-- url     : https://prove2.me/submissions/2b91e0e6-6fd8-4c91-86f6-4b1055830e2b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_good_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_commutator_l_sq
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
theorem _root_.solution (hC : SSComm) (hS : NabSS) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P u * mt P v - mt P v * mt P u) = -((mt P u - mt P v) * (mt P u - mt P v)) := by
  have h := congrArg star (commutator_l_sq P hC hS hP (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h
end Formalism.FourierDecayAlt.P.Mx6
