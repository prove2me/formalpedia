-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.partialDeriv_commute_nab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:50.874824+00:00
-- url     : https://prove2.me/submissions/6e7d05a6-6b22-4731-a447-649f4b3ab5cc

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_smul_fnP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zeta_free_of_variable
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_zi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_zbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_zf_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDeriv_mul_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_comm_eu
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_mk_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (l : Fin r) (a TT : ℝ) : pP l * nabE a TT = nabE a TT * pP l := by
  unfold nabE
  rw [zbP, ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn,
    ((zf_smul _ (zf_mul zf_zb (zf_ggi TT))) l).1, ((zf_smul _ (zf_mul zeta_free_of_variable (zf_ggi TT))) l).2, multiplierPair_zero, add_zero]
  congr 1
  apply mk_comm
  · exact comm_eu _ _ _ (zf_zi l).1
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu _ _ _ (zf_zbi l).2
end Formalism.FourierDecayAlt.P.Mx2
