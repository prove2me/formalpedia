-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.commute_l0_Um
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:12.082982+00:00
-- url     : https://prove2.me/submissions/43e189bd-a218-409e-92ba-5bb15b8fe2f4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_kap_comm_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_nabla_star_commute_gamma_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_absTerm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_nab_SSs
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
theorem _root_.solution (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (hLN : LevNab) (P : Par) (u : ℂ) :
    Commute (l0A P u) (ggiA P * Um P u) := by
  obtain ⟨_, _, _, _, _, nGi, _⟩ := hLN P
  have cGiz : Commute (ggiA P) (zbA P) := fn_comm P _ _ _ _
  have nGi' : nabA P * ggiA P = ggiA P * nabA P + -zbA P * ggiA P * ggiA P := by
    rw [nGi, neg_mul, neg_mul, sub_eq_add_neg]
  have h1 : Commute (nabA P) (ggiA P * Um P u) := by
    unfold Um; rw [Finset.mul_sum]
    exact Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nab P _).symm
      (nabla_star_commute_gamma_inv _ _ _ _ nGi' (by rw [nab_SSs hSc hN hSG P j hj, neg_mul, neg_mul, sub_neg_eq_add])
        (by rw [mul_neg, neg_mul, cGiz.eq])) (kap_comm_sc P _ _).symm)
  have h2 : Commute (zbA P * ggiA P) (ggiA P * Um P u) :=
    (cGiz.symm.mul_right (sc_Um hSc P _ _)).mul_left ((Commute.refl _).mul_right (sc_Um hSc P _ _))
  rw [lowering_constant_eq_shift]; exact (h1.neg_left).sub_left (h2.smul_left _)
end Formalism.FourierDecayAlt.P.Mx7
