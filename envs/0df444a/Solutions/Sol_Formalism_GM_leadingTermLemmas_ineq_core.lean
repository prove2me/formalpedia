-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.ineq_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:54.425992+00:00
-- url     : https://prove2.me/submissions/cbb4f43f-ef8a-48d4-ab91-b94b535032b2

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
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
open Finset
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (A : ℕ) (δ Kc p0 : ℝ) (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hp0 : 0 ≤ p0)
    (p nfv κ X X' Xc U U' Uc : ℕ → ℝ)
    (hX : ∀ l, 0 ≤ X l) (hX' : ∀ l, 0 ≤ X' l) (hU : ∀ l, 0 ≤ U l) (hU' : ∀ l, 0 ≤ U' l)
    (hXc : ∀ l, 2 * |Xc l| ≤ X l + X' l) (hUc : ∀ l, 2 * |Uc l| ≤ U l + U' l)
    (h0 : Uc 0 = Xc 0) (hnfv0 : nfv 0 = 1) (hpz : p 0 = p0) (hκ0 : κ 0 = 0)
    (hp : ∀ l, 1 ≤ l → l ≤ A → 0 ≤ p l ∧ p l * δ ≤ Kc * nfv l)
    (hnfv : ∀ l, 1 ≤ l → l ≤ A → 0 ≤ nfv l ∧ nfv l * δ ≤ κ l * nfv l) :
    |∑ l ∈ range (A + 1), p l * Uc l - p0 * ∑ l ∈ range (A + 1), nfv l * Xc l| ≤
      (Kc * ∑ l ∈ range (A + 1), nfv l * (U l + U' l) +
        p0 * ∑ l ∈ range (A + 1), κ l * nfv l * (X l + X' l)) / (2 * δ) := by
  rw [le_div_iff₀ (by positivity)]
  simp only [Finset.sum_range_succ' _ A, hpz, h0, hnfv0, hκ0]
  have t1 : ∀ i ∈ range A, |p (i + 1) * Uc (i + 1)| * (2 * δ) ≤ Kc * (nfv (i + 1) * (U (i + 1) + U' (i + 1))) := by
    intro i hi
    have hiA : i + 1 ≤ A := by simp at hi; omega
    obtain ⟨hpn, hpb⟩ := hp (i + 1) (by omega) hiA
    have := mul_le_mul hpb (hUc (i + 1)) (by positivity) (by nlinarith [(hnfv (i+1) (by omega) hiA).1])
    rw [abs_mul, abs_of_nonneg hpn]
    nlinarith
  have t2 : ∀ i ∈ range A, |nfv (i + 1) * Xc (i + 1)| * (2 * δ) ≤ κ (i + 1) * nfv (i + 1) * (X (i + 1) + X' (i + 1)) := by
    intro i hi
    have hiA : i + 1 ≤ A := by simp at hi; omega
    obtain ⟨hn, hnb⟩ := hnfv (i + 1) (by omega) hiA
    have hκn : 0 ≤ κ (i + 1) * nfv (i + 1) := by nlinarith
    have := mul_le_mul hnb (hXc (i + 1)) (by positivity) hκn
    rw [abs_mul, abs_of_nonneg hn]
    nlinarith
  have s1 := Finset.sum_le_sum t1
  have s2 := Finset.sum_le_sum t2
  rw [← Finset.sum_mul] at s1 s2
  have a1 := Finset.abs_sum_le_sum_abs (fun i => p (i + 1) * Uc (i + 1)) (range A)
  have a2 := Finset.abs_sum_le_sum_abs (fun i => nfv (i + 1) * Xc (i + 1)) (range A)
  have e1 : ∑ i ∈ range A, p (i + 1) * Uc (i + 1) + p0 * Xc 0 -
      p0 * (∑ i ∈ range A, nfv (i + 1) * Xc (i + 1) + 1 * Xc 0) =
      ∑ i ∈ range A, p (i + 1) * Uc (i + 1) - p0 * ∑ i ∈ range A, nfv (i + 1) * Xc (i + 1) := by ring
  rw [e1]
  have hpos1 : 0 ≤ Kc * (1 * (U 0 + U' 0)) := by have := hU 0; have := hU' 0; positivity
  have hsum_nn : 0 ≤ ∑ i ∈ range A, |nfv (i + 1) * Xc (i + 1)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc |∑ i ∈ range A, p (i + 1) * Uc (i + 1) - p0 * ∑ i ∈ range A, nfv (i + 1) * Xc (i + 1)| * (2 * δ)
      ≤ (|∑ i ∈ range A, p (i + 1) * Uc (i + 1)| + p0 * |∑ i ∈ range A, nfv (i + 1) * Xc (i + 1)|) * (2 * δ) := by
        gcongr
        calc _ ≤ |∑ i ∈ range A, p (i + 1) * Uc (i + 1)| + |p0 * ∑ i ∈ range A, nfv (i + 1) * Xc (i + 1)| :=
              abs_sub _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hp0]
    _ ≤ (∑ i ∈ range A, |p (i + 1) * Uc (i + 1)| + p0 * ∑ i ∈ range A, |nfv (i + 1) * Xc (i + 1)|) * (2 * δ) := by
        gcongr
    _ = (∑ i ∈ range A, |p (i + 1) * Uc (i + 1)|) * (2 * δ) +
          p0 * ((∑ i ∈ range A, |nfv (i + 1) * Xc (i + 1)|) * (2 * δ)) := by ring
    _ ≤ Kc * ∑ i ∈ range A, nfv (i + 1) * (U (i + 1) + U' (i + 1)) +
          p0 * ∑ i ∈ range A, κ (i + 1) * nfv (i + 1) * (X (i + 1) + X' (i + 1)) := by
        rw [Finset.mul_sum]
        exact add_le_add s1 (mul_le_mul_of_nonneg_left s2 hp0)
    _ ≤ _ := by
        rw [mul_add Kc, mul_add p0]
        simp only [zero_mul, add_zero]
        linarith
end Formalism.GM.leadingTermLemmas
