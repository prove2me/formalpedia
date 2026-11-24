-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_levels
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:29.566215+00:00
-- url     : https://prove2.me/submissions/4c8c2c0d-fb18-4958-9257-d8dec478bb7d

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_smul_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sum_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_smul_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sum_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_EE
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
theorem _root_.solution (hr : 1 ≤ r) (s : ℕ) (R : Finset ℕ) (u u' : ℕ → MvPolynomial σ K) (c d : ℕ → K)
    (α β α' β' : ℕ → ℕ) (hu : ∀ l ∈ R, BiHom w e (α l) (β l) (u l) ∧ tieF w e (u l) = 0)
    (hu' : ∀ l ∈ R, BiHom w e (α' l) (β' l) (u' l) ∧ tieF w e (u' l) = 0) :
    fk (∑ l ∈ R, c l • (tieE w e ^ (s + l)) (u l)) (∑ l ∈ R, d l • (tieE w e ^ (s + l)) (u' l)) =
      ∑ l ∈ R, c l * d l * (((s + l).descFactorial (s + l) *
        (α' l + β' l + r - 1 + (s + l)).descFactorial (s + l) : ℕ) : K) * fk (u l) (u' l) := by
  rw [fk_sum_left]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [fk_smul_left, fk_sum_right]
  have : ∀ l' ∈ R, fk ((tieE w e ^ (s + l)) (u l)) (d l' • (tieE w e ^ (s + l')) (u' l')) =
      if l = l' then d l' * ((((s + l').descFactorial (s + l') *
        (α' l' + β' l' + r - 1 + (s + l')).descFactorial (s + l') : ℕ) : K) * fk (u l) (u' l')) else 0 := by
    intro l' hl'
    rw [fk_smul_right, fk_EE hw he hwe hr (hu l hl).1 (hu l hl).2 (hu' l' hl').1 (hu' l' hl').2]
    by_cases h : l = l'
    · subst h; simp
    · rw [if_neg (by omega), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hl]
  ring
end Formalism.GM.leadingTermLemmas
