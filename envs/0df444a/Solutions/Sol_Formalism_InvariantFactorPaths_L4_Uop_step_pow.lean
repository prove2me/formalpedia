-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Uop_step_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:16.145663+00:00
-- url     : https://prove2.me/submissions/19dca273-a028-4c5f-ab8c-327ea7c9d8c8

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_comm_pow
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
theorem _root_.solution (c : ℤ) (x w : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : DDop p LL Cs a x = -w) (hw : DDop p LL Cs a w = 0) (k : ℕ)
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ((Uop p LL c Cs a) ^ (k + 1)) (x * G) = x * ((Uop p LL c Cs a) ^ (k + 1)) G +
      ((k + 1 : ℕ) : ℚ_[p]) • (w * ((Uop p LL c Cs a) ^ k) G) := by
  have h1 : ∀ G, Uop p LL c Cs a (x * G) = x * Uop p LL c Cs a G + w * G := by
    intro G
    rw [Uop_eq, Uop_eq, DDop_mul, hx]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  induction k generalizing G with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one, one_smul]
    exact h1 G
  | succ k ih =>
    have e0 : ((Uop p LL c Cs a) ^ (k + 1 + 1)) (x * G) =
        ((Uop p LL c Cs a) ^ (k + 1)) (Uop p LL c Cs a (x * G)) := by
      rw [pow_succ, Module.End.mul_apply]
    have e1 : ((Uop p LL c Cs a) ^ (k + 1 + 1)) G =
        ((Uop p LL c Cs a) ^ (k + 1)) (Uop p LL c Cs a G) := by
      rw [pow_succ, Module.End.mul_apply]
    have e2 : ((Uop p LL c Cs a) ^ (k + 1)) G = ((Uop p LL c Cs a) ^ k) (Uop p LL c Cs a G) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [e0, h1, map_add, ih, Uop_comm_pow LL Cs a c w hw (k + 1), ← e1, ← e2]
    push_cast
    simp only [MvPolynomial.smul_eq_C_mul, map_add, map_one, map_natCast]
    ring
end Formalism.InvariantFactorPaths.L4
