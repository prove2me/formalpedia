-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.fischerAdjointness_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:31.005187+00:00
-- url     : https://prove2.me/submissions/2d69e059-d205-490d-9141-62125ada38d0

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_left__85aaa0c1d77b
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_neg_left__eec94d6616dc
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_sum_left__a0ab5af836e3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_sum_right__325424ac65a7
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_X_mul__e23e914b465e
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : FockAdj := by
  intro p _ N r LL j c d F G
  have key : ∀ (a b : Fin N × Fin r) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      fock p (X a * pderiv b F) G = fock p F (X b * pderiv a G) := by
    intro a b F G
    rw [fock_X_mul', fock_symm' F, fock_X_mul', fock_symm']
  unfold glAct
  rw [LinearMap.sum_apply, LinearMap.sum_apply, fock_sum_left', fock_sum_right']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2
  · simpa using key (i, c) (i, d) F G
  · simp [fock_neg_left', fock_neg_right', key]
  · simp [fock_zero_left', fock_zero_right']
end Formalism.InvariantFactorPaths.PW
