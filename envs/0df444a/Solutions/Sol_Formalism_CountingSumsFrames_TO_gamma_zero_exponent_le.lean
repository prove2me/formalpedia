-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.gamma_zero_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:37.549538+00:00
-- url     : https://prove2.me/submissions/8829d194-063e-4e75-9469-3e4a6a7a21f8

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
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
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (K r a : ℕ) (hr : 1 ≤ r) (κ : ℝ) (hκ : ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    (K + 2) * (r * Nat.log p (2 * a)) ≤ ⌈κ⌉₊ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hlog : (Nat.log p (2 * a) : ℝ) ≤ lgV2 p a r := by
    unfold lgV2
    have h0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1 (by linarith)
    by_cases ha : a = 0
    · have hz : Nat.log p (2 * a) = 0 := by rw [ha]; simp
      rw [hz, Nat.cast_zero]
      linarith
    · have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p ((2 * a : ℕ) : ℝ) := Real.natLog_le_logb _ _
      have hapos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
      have h2 : Real.logb p ((2 * a : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
        apply Real.logb_le_logb_of_le hp1
        · push_cast; linarith
        · push_cast; linarith
      linarith
  have hl0 : (0 : ℝ) ≤ (Nat.log p (2 * a) : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h3 : (((K + 2) * (r * Nat.log p (2 * a)) : ℕ) : ℝ) ≤ κ := by
    push_cast
    calc ((K : ℝ) + 2) * ((r : ℝ) * (Nat.log p (2 * a) : ℝ))
        ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 * lgV2 p a r) := by
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          apply mul_le_mul _ hlog hl0 (by positivity)
          nlinarith
      _ = ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r := by ring
      _ ≤ κ := hκ
  exact_mod_cast h3.trans (Nat.le_ceil κ)
end Formalism.CountingSumsFrames.TO
