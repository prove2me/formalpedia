-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.commute_m0_Ul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:12.024831+00:00
-- url     : https://prove2.me/submissions/f0aa643b-ebb6-452f-aa61-a6e6a8869b2d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_nabs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_nabla_star_commute_gamma_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absTerm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_raising_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_Ul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hN : NabSS) (hLNs : LevNabs) (P : Par) (u : ℂ) :
    Commute (m0A P u) (ggiA P * Ul P u) := by
  obtain ⟨_, _, _, _, _, nsGi, _⟩ := hLNs P
  have cGiz : Commute (ggiA P) (zA P) := fn_comm P _ _ _ _
  have h1 : Commute (nabsA P) (ggiA P * Ul P u) := by
    unfold Ul; rw [Finset.mul_sum]
    exact Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nabs P _).symm
      (nabla_star_commute_gamma_inv _ _ _ _ nsGi (hN P j hj).2 cGiz.eq) (kap_comm_sc P _ _).symm)
  have h2 : Commute (zA P * ggiA P) (ggiA P * Ul P u) :=
    (cGiz.symm.mul_right (sc_Ul hSc P _ _)).mul_left ((Commute.refl _).mul_right (sc_Ul hSc P _ _))
  rw [raising_constant_eq_shift]; exact (h1.neg_left).sub_left (h2.smul_left _)
end Formalism.FourierDecayAlt.P.Mx7
