-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.F_E_pow_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:37.423708+00:00
-- url     : https://prove2.me/submissions/30e1b8b3-1668-4283-871d-865b1ff29d29

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_E_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_FE_one
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
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {a b : ℕ} {y : MvPolynomial σ K} (hy : BiHom w e a b y) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) y) =
      (tieE w e ^ (j + 1)) (tieF w e y) + (((j + 1) * (a + b + r + j) : ℕ) : K) • (tieE w e ^ j) y := by
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, one_mul, add_zero]
    exact FE_one hw he hwe hy
  | succ j ih =>
    have h2 := biHom_E_pow hw he hwe hy (j + 1)
    rw [show tieE w e ^ (j + 1 + 1) = tieE w e * tieE w e ^ (j + 1) from pow_succ' _ _,
      Module.End.mul_apply, FE_one hw he hwe h2, ih, map_add, map_smul, ← Module.End.mul_apply,
      ← pow_succ', ← Module.End.mul_apply (tieE w e) (tieE w e ^ j), ← pow_succ', add_assoc, ← add_smul]
    congr 2
    push_cast; ring
end Formalism.GM.leadingTermLemmas
