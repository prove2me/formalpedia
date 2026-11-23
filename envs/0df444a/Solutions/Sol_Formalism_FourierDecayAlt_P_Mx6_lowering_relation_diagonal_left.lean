-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.lowering_relation_diagonal_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:30.329148+00:00
-- url     : https://prove2.me/submissions/f50afdf3-13f5-450a-9b71-b5145ea99bce

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_commutator_identity_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L3_Lam1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lam_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_gG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Gg__2bb78f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_g__c17bb9
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cc_g
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_x_N
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_half

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
    (u - v) • (t22 P u * lA P v - lA P v * t22 P u) = -(t22 P u * (lA P u - lA P v)) := by
  have h := commutator_identity_one (nabA P) (cc P) (ggA P) (ggiA P) (xA P u) (abelian₂ P u) (abelian₂ P v) (u + 1 / 2) (v + 1 / 2)
    (N_g P) (x_N P u) (gG P) (Gg P) (cc_g P) (kap_sc P _ _) (kap_sc P _ _) (kap_cc P _)
    (Lam_sc P _ _) (Lam_sc P _ _) (by rw [half]; exact L3.Lam1 P u v hu hv)
  rw [half] at h
  rw [t22, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h
end Formalism.FourierDecayAlt.P.Mx6
