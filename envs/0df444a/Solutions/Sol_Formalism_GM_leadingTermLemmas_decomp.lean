-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:48.72208+00:00
-- url     : https://prove2.me/submissions/a677a915-63f7-4f9b-b3a6-6d1150d60edf

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_zero
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_smul
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sub
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sum
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_E
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_E_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_F
import Theorems.Thm_Formalism_GM_F_E_pow
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
import Theorems.Thm_Formalism_GM_euler_e_of_biHom
import Theorems.Thm_Formalism_GM_euler_w_of_biHom
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
theorem _root_.solution (hr : 1 ≤ r) : ∀ (a b : ℕ) (y : MvPolynomial σ K), BiHom w e a b y →
    ∃ u : ℕ → MvPolynomial σ K, y = ∑ l ∈ range (a + 1), (tieE w e ^ l) (u l) ∧
      ∀ l ∈ range (a + 1), tieF w e (u l) = 0 ∧ BiHom w e (a - l) (b - l) (u l) ∧ (u l ≠ 0 → l ≤ b) := by
  intro a
  induction a with
  | zero =>
    intro b y hy
    refine ⟨fun _ => y, by simp, fun l hl => ?_⟩
    have hl0 : l = 0 := by simp only [Finset.mem_range] at hl; omega
    subst hl0
    exact ⟨(biHom_F hw he hwe hy).2 (Or.inl rfl), by simpa using hy, fun _ => Nat.zero_le _⟩
  | succ a ih =>
    intro b y hy
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      refine ⟨fun l => if l = 0 then y else 0, ?_, fun l hl => ?_⟩
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro l _ hl; simp [hl]
        · simp
      · by_cases h : l = 0
        · subst h
          exact ⟨by simpa using (biHom_F hw he hwe hy).2 (Or.inr rfl), by simpa using hy, fun _ => le_rfl⟩
        · simp only [h, if_false]
          exact ⟨map_zero _, biHom_zero _ _, fun h' => absurd rfl h'⟩
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hFy := (biHom_F hw he hwe hy).1
      simp only [Nat.add_sub_cancel] at hFy
      obtain ⟨wl, hwl, hwc⟩ := ih b' _ hFy
      let κ : ℕ → ℕ := fun l => (l + 1) * ((a - l) + (b' - l) + r + l)
      have hκ : ∀ l, (κ l : K) ≠ 0 := fun l => by
        have : 0 < κ l := Nat.mul_pos (by omega) (by omega)
        exact_mod_cast this.ne'
      let x := ∑ l ∈ range (a + 1), ((κ l : K))⁻¹ • (tieE w e ^ l) (wl l)
      have hFE : ∀ l ∈ range (a + 1), tieF w e ((tieE w e ^ (l + 1)) (wl l)) = (κ l : K) • (tieE w e ^ l) (wl l) := by
        intro l hl
        have hc := hwc l hl
        exact F_E_pow hw he hwe _ _ _ (euler_w_of_biHom w e hc.2.1) (euler_e_of_biHom w e hc.2.1) hc.1 l
      have hEx : tieE w e x = ∑ l ∈ range (a + 1), ((κ l : K))⁻¹ • (tieE w e ^ (l + 1)) (wl l) := by
        simp only [x, map_sum, map_smul]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [pow_succ', Module.End.mul_apply]
      have hFEx : tieF w e (tieE w e x) = tieF w e y := by
        rw [hEx, map_sum, hwl]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        rw [map_smul, hFE l hl, smul_smul, inv_mul_cancel₀ (hκ l), one_smul]
      have hxB : BiHom w e a b' x := by
        apply biHom_sum
        intro l hl
        apply biHom_smul
        by_cases h0 : wl l = 0
        · rw [h0, map_zero]; exact biHom_zero _ _
        · have hc := hwc l hl
          have hlb := hc.2.2 h0
          have hla : l ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have := biHom_E_pow hw he hwe hc.2.1 l
          rwa [Nat.sub_add_cancel hla, Nat.sub_add_cancel hlb] at this
      refine ⟨fun l => if l = 0 then y - tieE w e x else ((κ (l - 1) : K))⁻¹ • wl (l - 1), ?_, fun l hl => ?_⟩
      · rw [Finset.sum_range_succ']
        simp only [if_true, pow_zero, Module.End.one_apply, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [hEx]
        have : ∀ l ∈ range (a + 1), (tieE w e ^ (l + 1)) (((κ l : K))⁻¹ • wl l) =
            ((κ l : K))⁻¹ • (tieE w e ^ (l + 1)) (wl l) := fun l _ => map_smul _ _ _
        rw [Finset.sum_congr rfl this]
        abel
      · by_cases h : l = 0
        · subst h
          simp only [if_true, Nat.sub_zero]
          refine ⟨by rw [map_sub, hFEx, sub_self], biHom_sub hy (biHom_E hw he hwe hxB), fun _ => Nat.zero_le _⟩
        · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
          simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          have hl' : l' ∈ range (a + 1) := by
            simp only [Finset.mem_range] at hl ⊢; omega
          have hc := hwc l' hl'
          refine ⟨by rw [map_smul, hc.1, smul_zero], ?_, fun h0 => ?_⟩
          · rw [Nat.add_sub_add_right, Nat.add_sub_add_right]; exact biHom_smul _ hc.2.1
          · have : wl l' ≠ 0 := fun h1 => h0 (by rw [h1, smul_zero])
            have := hc.2.2 this; omega
end Formalism.GM.leadingTermLemmas
