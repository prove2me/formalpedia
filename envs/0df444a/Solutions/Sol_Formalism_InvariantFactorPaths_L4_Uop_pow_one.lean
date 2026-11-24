-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Uop_pow_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:34.394796+00:00
-- url     : https://prove2.me/submissions/ce5bbfaa-d242-4dbd-87e8-2b7cd7efc700

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_fact_choose_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_shift_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_last
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
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (c : ℤ) (k : ℕ) :
    ((Uop p LL c Cs a) ^ k) 1 =
      (((k.factorial : ℤ) * Ring.choose c k : ℤ) : ℚ_[p]) • (X (Fin.last K, a) ^ k) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    have hU1 : Uop p LL c Cs a 1 = ((c : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * 1) := by
      rw [Uop_eq]
      have h0 : DDop p LL Cs a 1 = 0 := by
        have h2 := DDop_mul (p := p) LL Cs a 1 1
        rw [one_mul, one_mul, mul_one] at h2
        linear_combination -h2
      rw [h0, sub_zero]
    have hq := DDop_last (p := p) LL Cs a a
    have key := Uop_shift_pow LL Cs a (c - 1) 1 (X (Fin.last K, a)) hq k 1
    rw [sub_add_cancel] at key
    rw [pow_succ (Uop p LL c Cs a) k, Module.End.mul_apply, hU1, map_smul, key, ih (c - 1), fact_choose_succ]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_mul]
    ring
end Formalism.InvariantFactorPaths.L4
