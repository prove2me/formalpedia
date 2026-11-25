-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:45.059274+00:00
-- url     : https://prove2.me/submissions/ddcb4854-b233-4bc5-bd07-512811196c0d

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_E
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_self_nonneg
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_abs_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_add
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_levels
import Theorems.Thm_Formalism_GM_leadingTermLemmas_decomp
import Theorems.Thm_Formalism_GM_leadingTermLemmas_ineq_core
import Theorems.Thm_Formalism_GM_leadingTermLemmas_Kc_nonneg
import Theorems.Thm_Formalism_GM_leadingTermLemmas_kappa_zero_nonneg
import Theorems.Thm_Formalism_GM_leadingTermLemmas_decompE
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
import Theorems.Thm_Formalism_GM_Top_levelAct
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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (hr : 1 ≤ r) (o n z t : ℕ) (ht : t ≤ o) (hon : o < n)
    (v0 y v0' y' : MvPolynomial σ ℝ)
    (hv0 : BiHom w e (o - t) (n - t) v0) (hy : BiHom w e (o - t - 1) (n - t - 1) y)
    (hy0 : y ≠ 0 → 1 ≤ o - t ∧ 1 ≤ n - t)
    (hv0' : BiHom w e (o - t) (n - t) v0') (hy' : BiHom w e (o - t - 1) (n - t - 1) y')
    (hy0' : y' ≠ 0 → 1 ≤ o - t ∧ 1 ≤ n - t) :
    |fk (tiePhi w e o n z ((tieE w e ^ t) (v0 + tieE w e y))) ((tieE w e ^ t) (v0' + tieE w e y'))
        - kap0 o n z t r * fk v0 v0'| ≤
      (Kc o z * (fk (v0 + tieE w e y) (v0 + tieE w e y) + fk (v0' + tieE w e y') (v0' + tieE w e y')) +
        kap0 o n z t r * (fk (tieF w e v0) (tieF w e v0) + fk (tieF w e v0') (tieF w e v0'))) /
        (2 * ((n - o : ℕ) : ℝ)) := by
  set A := o - t with hAdef
  set Bn := n - t with hBdef
  have hAB : A ≤ Bn := by omega
  obtain ⟨x, hx, hxc⟩ := decomp hw he hwe hr A Bn v0 hv0
  obtain ⟨x', hx', hxc'⟩ := decomp hw he hwe hr A Bn v0' hv0'
  obtain ⟨yl, hyl, hylc⟩ := decompE hw he hwe hr A Bn y hy hy0
  obtain ⟨yl', hyl', hylc'⟩ := decompE hw he hwe hr A Bn y' hy' hy0'
  let u : ℕ → MvPolynomial σ ℝ := fun l => x l + (if l = 0 then 0 else yl (l - 1))
  let u' : ℕ → MvPolynomial σ ℝ := fun l => x' l + (if l = 0 then 0 else yl' (l - 1))

  have hsumE : ∀ (xx : ℕ → MvPolynomial σ ℝ) (yy : ℕ → MvPolynomial σ ℝ),
      ∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l + (if l = 0 then 0 else yy (l - 1))) =
        ∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l) + ∑ l ∈ range A, (tieE w e ^ (l + 1)) (yy l) := by
    intro xx yy
    simp only [map_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_range_succ']
    simp
  have hv : v0 + tieE w e y = ∑ l ∈ range (A + 1), (tieE w e ^ l) (u l) := by
    rw [hsumE, ← hx, ← hyl]
  have hv' : v0' + tieE w e y' = ∑ l ∈ range (A + 1), (tieE w e ^ l) (u' l) := by
    rw [hsumE, ← hx', ← hyl']
  have hucond : ∀ (xx yy : ℕ → MvPolynomial σ ℝ),
      (∀ l ∈ range (A + 1), tieF w e (xx l) = 0 ∧ BiHom w e (A - l) (Bn - l) (xx l) ∧ (xx l ≠ 0 → l ≤ Bn)) →
      (∀ l ∈ range A, tieF w e (yy l) = 0 ∧ BiHom w e (A - 1 - l) (Bn - 1 - l) (yy l)) →
      ∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (xx l + (if l = 0 then 0 else yy (l - 1))) ∧
        tieF w e (xx l + (if l = 0 then 0 else yy (l - 1))) = 0 := by
    intro xx yy hxx hyy l hl
    by_cases h0 : l = 0
    · subst h0; simpa using ⟨(hxx 0 hl).2.1, (hxx 0 hl).1⟩
    · have hl1 : l - 1 ∈ range A := by simp only [Finset.mem_range] at hl ⊢; omega
      simp only [h0, if_false]
      have hb := (hyy (l - 1) hl1).2
      rw [show A - 1 - (l - 1) = A - l by omega, show Bn - 1 - (l - 1) = Bn - l by omega] at hb
      exact ⟨biHom_add (hxx l hl).2.1 hb, by rw [map_add, (hxx l hl).1, (hyy (l - 1) hl1).1, add_zero]⟩
  have hu := hucond x yl hxc hylc
  have hu' := hucond x' yl' hxc' hylc'

  let c : ℕ → ℝ := fun l => ((z + (t + l)).choose (t + l) : ℝ) / ((o + n + r + z - 1).choose (t + l) : ℝ)
  have hphi : tiePhi w e o n z ((tieE w e ^ t) (v0 + tieE w e y)) =
      ∑ l ∈ range (A + 1), c l • (tieE w e ^ (t + l)) (u l) := by
    rw [hv, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hlA : l ≤ A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [show (tieE w e ^ t) ((tieE w e ^ l) (u l)) = (tieE w e ^ (t + l)) (u l) by
      rw [pow_add, Module.End.mul_apply]]
    have hB := (hu l hl).1
    rw [show A - l = o - (t + l) by omega, show Bn - l = n - (t + l) by omega] at hB
    exact Formalism.GM.Top.levelAct ℝ σ r w e hw he hwe hr o n z (t + l) (u l) (by omega) (by omega) (hu l hl).2 hB
  have hEt : (tieE w e ^ t) (v0' + tieE w e y') =
      ∑ l ∈ range (A + 1), (fun _ => (1 : ℝ)) l • (tieE w e ^ (t + l)) (u' l) := by
    rw [hv', map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_smul, pow_add, Module.End.mul_apply]
  have hBform := fk_levels hw he hwe hr t (range (A + 1)) u u' c (fun _ => 1)
    (fun l => A - l) (fun l => Bn - l) (fun l => A - l) (fun l => Bn - l)
    (fun l hl => ⟨(hu l hl).1, (hu l hl).2⟩) (fun l hl => ⟨(hu' l hl).1, (hu' l hl).2⟩)

  have hlev0 : ∀ (uu uu' : ℕ → MvPolynomial σ ℝ),
      (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (uu l) ∧ tieF w e (uu l) = 0) →
      (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (uu' l) ∧ tieF w e (uu' l) = 0) →
      (cc : ℕ → ℝ) →
      fk (∑ l ∈ range (A + 1), cc l • (tieE w e ^ l) (uu l)) (∑ l ∈ range (A + 1), (tieE w e ^ l) (uu' l)) =
        ∑ l ∈ range (A + 1), cc l * 1 * (((0 + l).descFactorial (0 + l) *
          ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ) * fk (uu l) (uu' l) := by
    intro uu uu' h1 h2 cc
    have := fk_levels hw he hwe hr 0 (range (A + 1)) uu uu' cc (fun _ => 1)
      (fun l => A - l) (fun l => Bn - l) (fun l => A - l) (fun l => Bn - l) h1 h2
    simpa using this
  have hxc2 : ∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (x l) ∧ tieF w e (x l) = 0 :=
    fun l hl => ⟨(hxc l hl).2.1, (hxc l hl).1⟩
  have hxc2' : ∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (x' l) ∧ tieF w e (x' l) = 0 :=
    fun l hl => ⟨(hxc' l hl).2.1, (hxc' l hl).1⟩
  have h1s : ∀ (uu : ℕ → MvPolynomial σ ℝ),
      ∑ l ∈ range (A + 1), (tieE w e ^ l) (uu l) = ∑ l ∈ range (A + 1), (fun _ => (1 : ℝ)) l • (tieE w e ^ l) (uu l) := by
    intro uu; simp
  have hv0v0' := hlev0 x x' hxc2 hxc2' (fun _ => 1)
  rw [← h1s, ← hx, ← hx'] at hv0v0'
  have hvv := hlev0 u u hu hu (fun _ => 1)
  rw [← h1s, ← hv] at hvv
  have hvv' := hlev0 u' u' hu' hu' (fun _ => 1)
  rw [← h1s, ← hv'] at hvv'

  let κ : ℕ → ℕ := fun l => l * ((A - l) + (Bn - l) + r + (l - 1))
  have hEF : ∀ (xx : ℕ → MvPolynomial σ ℝ), (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (xx l) ∧ tieF w e (xx l) = 0) →
      tieE w e (tieF w e (∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l))) =
        ∑ l ∈ range (A + 1), ((κ l : ℕ) : ℝ) • (tieE w e ^ l) (xx l) := by
    intro xx hxx
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    by_cases h0 : l = 0
    · subst h0; simp [(hxx 0 hl).2, κ]
    · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
      rw [F_E_pow hw he hwe _ _ _ (euler_w_of_biHom w e (hxx _ hl).1) (euler_e_of_biHom w e (hxx _ hl).1)
        (hxx _ hl).2 j, map_smul, ← Module.End.mul_apply, ← pow_succ']
      simp only [κ, Nat.add_sub_cancel]
  have hFF : ∀ (xx : ℕ → MvPolynomial σ ℝ), (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (xx l) ∧ tieF w e (xx l) = 0) →
      fk (tieF w e (∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l))) (tieF w e (∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l))) =
        ∑ l ∈ range (A + 1), ((κ l : ℕ) : ℝ) * 1 * (((0 + l).descFactorial (0 + l) *
          ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ) * fk (xx l) (xx l) := by
    intro xx hxx
    rw [← fk_E, hEF xx hxx]
    exact hlev0 xx xx hxx hxx _
  have hF0 := hFF x hxc2
  rw [← hx] at hF0
  have hF0' := hFF x' hxc2'
  rw [← hx'] at hF0'

  rw [hphi, hEt, hBform, hv0v0', hvv, hvv', hF0, hF0']
  have hδ : (0 : ℝ) < ((n - o : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - o)
  have key := ineq_core A ((n - o : ℕ) : ℝ) (Kc o z) (kap0 o n z t r) hδ (Kc_nonneg o z) (kappa_zero_nonneg o n z t r)
    (fun l => c l * 1 * (((t + l).descFactorial (t + l) *
        ((A - l) + (Bn - l) + r - 1 + (t + l)).descFactorial (t + l) : ℕ) : ℝ))
    (fun l => 1 * 1 * (((0 + l).descFactorial (0 + l) * ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ))
    (fun l => ((κ l : ℕ) : ℝ))
    (fun l => fk (x l) (x l)) (fun l => fk (x' l) (x' l)) (fun l => fk (x l) (x' l))
    (fun l => fk (u l) (u l)) (fun l => fk (u' l) (u' l)) (fun l => fk (u l) (u' l))
    (fun l => fk_self_nonneg _) (fun l => fk_self_nonneg _) (fun l => fk_self_nonneg _) (fun l => fk_self_nonneg _)
    (fun l => fk_abs_le _ _) (fun l => fk_abs_le _ _)
    (by simp [u, u']) (by simp) ?_ (by simp [κ]) ?_ ?_
  · convert key using 2
    rw [mul_add, mul_add]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  · simp only [c, kap0, Nat.add_zero, Nat.sub_zero, Nat.descFactorial_self, mul_one]
    rw [show A + Bn + r - 1 + t = o + n + r - 1 - t by omega]
  · intro l hl1 hlA
    set L := t + l with hL
    have hLo : L ≤ o := by omega
    have hchpos : 0 < (o + n + r + z - 1).choose L := Nat.choose_pos (by omega)
    have hD : ((A - l) + (Bn - l) + r - 1 + L).descFactorial L ≤ L.factorial * (o + n + r + z - 1).choose L := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le _ (by omega)
    have hpl : c l * 1 * ((L.descFactorial L * ((A - l) + (Bn - l) + r - 1 + L).descFactorial L : ℕ) : ℝ) ≤
        (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ) := by
      simp only [c, mul_one, Nat.descFactorial_self]
      rw [← hL, div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hchpos)]
      have : ((L.factorial * ((A - l) + (Bn - l) + r - 1 + L).descFactorial L : ℕ) : ℝ) ≤
          ((L.factorial * (L.factorial * (o + n + r + z - 1).choose L) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left _ hD
      push_cast at this ⊢
      nlinarith [(Nat.cast_nonneg ((z + L).choose L) : (0:ℝ) ≤ _)]
    have hterm : (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ) ≤ Kc o z := by
      unfold Kc
      exact Finset.single_le_sum (f := fun L => (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega))
    have hnf : ((n - o : ℕ) : ℝ) ≤ 1 * 1 * (((0 + l).descFactorial (0 + l) *
        ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ) := by
      simp only [one_mul, zero_add, Nat.descFactorial_self]
      have h1 := Nat.pow_sub_le_descFactorial ((A - l) + (Bn - l) + r - 1 + l) l
      have h2 : n - o ≤ ((A - l) + (Bn - l) + r - 1 + l + 1 - l) := by omega
      have h3 : ((A - l) + (Bn - l) + r - 1 + l + 1 - l) ≤ ((A - l) + (Bn - l) + r - 1 + l + 1 - l) ^ l :=
        Nat.le_self_pow (by omega) _
      have h4 : 1 ≤ l.factorial := Nat.factorial_pos l
      have : n - o ≤ l.factorial * ((A - l) + (Bn - l) + r - 1 + l).descFactorial l :=
        le_trans (le_trans h2 (le_trans h3 h1)) (Nat.le_mul_of_pos_left _ h4)
      exact_mod_cast this
    have hpnn : 0 ≤ c l * 1 * ((L.descFactorial L * ((A - l) + (Bn - l) + r - 1 + L).descFactorial L : ℕ) : ℝ) := by
      simp only [c]; positivity
    refine ⟨hpnn, ?_⟩
    calc _ ≤ (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ) * ((n - o : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hpl hδ.le
      _ ≤ Kc o z * ((n - o : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hterm hδ.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hnf (Kc_nonneg o z)
  · intro l hl1 hlA
    refine ⟨by positivity, ?_⟩
    have hk : n - o ≤ κ l := by
      simp only [κ]
      have : n - o ≤ (A - l) + (Bn - l) + r + (l - 1) := by omega
      exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    have hk' : ((n - o : ℕ) : ℝ) ≤ ((κ l : ℕ) : ℝ) := by exact_mod_cast hk
    exact mul_le_mul_of_nonneg_left hk' (by positivity) |>.trans_eq (by ring)
end Formalism.GM.leadingTermLemmas
