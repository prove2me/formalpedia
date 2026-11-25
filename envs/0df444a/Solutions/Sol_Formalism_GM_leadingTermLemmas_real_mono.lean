-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.real_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:21.664521+00:00
-- url     : https://prove2.me/submissions/5c645425-dd9a-43ce-9958-d616261be490

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_zero_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_zero_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_core
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wW_inj
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_wW_ne_e__a87a32810661
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_eta_lim
import Theorems.Thm_Formalism_GM_leadingTermLemmas_snoc_degree_last_weight
import Theorems.Thm_Formalism_GM_leadingTermLemmas_snoc_deg_eta
import Theorems.Thm_Formalism_GM_leadingTermLemmas_leading_vector_add_linked
import Theorems.Thm_Formalism_GM_leadingTermLemmas_frz_shape
import Theorems.Thm_Formalism_GM_leadingTermLemmas_linked_map_leading_vector
import Theorems.Thm_Formalism_GM_leadingTermLemmas_m_W_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_o_le_S
import Theorems.Thm_Formalism_GM_leadingTermLemmas_bihomogeneous_leading_vector
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_Yh
import Theorems.Thm_Formalism_GM_leadingTermLemmas_Yh_ne
import Theorems.Thm_Formalism_GM_leadingTermLemmas_gv_eta_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_gF_eta_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_sq_eta_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_kappa_zero_tendsto_factorials
import Theorems.Thm_Formalism_GM_leadingTermLemmas_chooseA_lim
import Theorems.Thm_Formalism_GM_leadingTermLemmas_inv_sub_lim
import Theorems.Thm_Formalism_GM_leadingTermLemmas_limit_value
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_hX2
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
open MvPolynomial Finset Formalism.GM Filter Topology
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (hr : 1 ≤ r) (hv : LL.vec (Fin.last N) = true) (z e : ℕ)
    (m m' : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (hm' : M.MultiDeg LL m')
    (hme : e ≤ m (Fin.last N, ρ)) (hme' : e ≤ m' (Fin.last N, ρ)) :
    Tendsto (fun n : ℕ => gamK ℝ LL ρ z n (monomial m 1) (monomial m' 1) /
        (n : ℝ) ^ (LL.total + LL.deg (Fin.last N) - e)) atTop
      (𝓝 ((((e.factorial * (z + e).choose e : ℕ) : ℝ) * fk (inMono (K := ℝ) ρ e m) (inMono ρ e m')) /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)))) := by
  have heo : e ≤ LL.deg (Fin.last N) := le_trans hme (m_W_le LL ρ m hm)
  have hoS : LL.deg (Fin.last N) ≤ LL.total := o_le_S LL
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  set P : ℝ := ((S.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ) with hP
  have hPpos : 0 < P := by
    have : 0 < ∏ i, ((LL.deg i).factorial : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos _)
    have h2 : (0 : ℝ) < ((S.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity

  let Bf : ℕ → ℝ := fun n => fk (tiePhi (wW (N := N)) eη o n z
      ((tieE (wW (N := N)) eη ^ e) (V0 LL ρ e m n + tieE (wW (N := N)) eη (Yh LL ρ e m n))))
      ((tieE (wW (N := N)) eη ^ e) (V0 LL ρ e m' n + tieE (wW (N := N)) eη (Yh LL ρ e m' n)))
  have hgam : ∀ n, gamK ℝ LL ρ z n (monomial m 1) (monomial m' 1) =
      ((o + n + r + z - 1).choose o : ℝ) * Bf n / ((((n - S).factorial : ℕ) : ℝ) * P) := by
    intro n
    unfold gamK
    rw [snoc_degree_last_weight, snoc_deg_eta, frz_shape LL ρ e hv m hme, frz_shape LL ρ e hv m' hme']
    simp only [Bf, hP]
    push_cast
    ring

  let Q : ℕ → ℝ := fun n => (((n - S).factorial : ℕ) : ℝ) * (n : ℝ) ^ (S - e)
  let i0 : Fin (N + 1 + 1) × Fin r := (Fin.last (N + 1), ρ)
  have hX1 := fk_eta_lim i0 S (S - e) (gv LL ρ e m) (gv LL ρ e m) (gv_eta_le (K := ℝ) LL ρ e m hm hme)
  have hX2 := fk_eta_lim i0 S (S - e) (gv LL ρ e m') (gv LL ρ e m') (gv_eta_le (K := ℝ) LL ρ e m' hm' hme')
  have hY1 := fk_eta_lim i0 S (S - e) (gF LL ρ e m) (gF LL ρ e m) (gF_eta_le (K := ℝ) LL ρ e m hm hme)
  have hY2 := fk_eta_lim i0 S (S - e) (gF LL ρ e m') (gF LL ρ e m') (gF_eta_le (K := ℝ) LL ρ e m' hm' hme')
  set T : ℝ := if m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e then
          ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
            (if M (Fin.last (N + 1), ρ) = S - e then 1 / ((S - e).factorial : ℝ) else 0)
        else 0 with hT
  have hf3 : Tendsto (fun n => fk (V0 (K := ℝ) LL ρ e m n) (V0 LL ρ e m' n) / Q n) atTop (𝓝 T) := by
    by_cases h : m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e
    · rw [hT, if_pos h]
      have := fk_eta_lim i0 S (S - e) (sq (K := ℝ) LL ρ m) (sq (K := ℝ) LL ρ m') (sq_eta_le (K := ℝ) LL ρ e m hm h.1)
      refine this.congr' (Eventually.of_forall (fun n => ?_))
      simp only [V0, if_pos h.1, if_pos h.2, Q, i0]
      rfl
    · rw [hT, if_neg h]
      refine tendsto_const_nhds.congr' (Eventually.of_forall (fun n => ?_))
      simp only [V0]
      by_cases h1 : m (Fin.last N, ρ) = e
      · rw [if_neg (fun h2 => h ⟨h1, h2⟩), fk_zero_right, zero_div]
      · rw [if_neg h1, fk_zero_left, zero_div]

  let f4 : ℕ → ℝ := fun n => (Bf n - kap0 o n z e r * fk (V0 LL ρ e m n) (V0 LL ρ e m' n)) / Q n
  let bd : ℕ → ℝ := fun n =>
    (Kc o z * (fk (X i0 ^ (n - S) * gv LL ρ e m) (X i0 ^ (n - S) * gv LL ρ e m) / Q n +
        fk (X i0 ^ (n - S) * gv LL ρ e m') (X i0 ^ (n - S) * gv LL ρ e m') / Q n) +
      kap0 o n z e r * (fk (X i0 ^ (n - S) * gF LL ρ e m) (X i0 ^ (n - S) * gF LL ρ e m) / Q n +
        fk (X i0 ^ (n - S) * gF LL ρ e m') (X i0 ^ (n - S) * gF LL ρ e m') / Q n)) *
      (1 / (2 * ((n - o : ℕ) : ℝ)))
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have := (((hX1.add hX2).const_mul (Kc o z)).add ((kappa_zero_tendsto_factorials o z e r).mul (hY1.add hY2))).mul (inv_sub_lim o)
    rw [mul_zero] at this
    exact this
  have hf4 : Tendsto f4 atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [eventually_ge_atTop (S + 1)] with n hn
    have hon : o < n := by omega
    have hc := core wW_inj eη_inj wW_ne_eη hr o n z e heo hon (V0 (K := ℝ) LL ρ e m n) (Yh LL ρ e m n)
      (V0 LL ρ e m' n) (Yh LL ρ e m' n)
      (bihomogeneous_leading_vector LL ρ e m hm hme n (by omega)) (biHom_Yh LL ρ e m hm hme n (by omega)) (Yh_ne LL ρ e m hm hme n (by omega))
      (bihomogeneous_leading_vector LL ρ e m' hm' hme' n (by omega)) (biHom_Yh LL ρ e m' hm' hme' n (by omega))
      (Yh_ne LL ρ e m' hm' hme' n (by omega))
    rw [leading_vector_add_linked LL ρ e m hme, leading_vector_add_linked LL ρ e m' hme', linked_map_leading_vector LL ρ e hv m, linked_map_leading_vector LL ρ e hv m'] at hc
    have hBf : Bf n = fk (tiePhi (wW (N := N)) eη o n z ((tieE (wW (N := N)) eη ^ e)
        (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gv LL ρ e m)))
        ((tieE (wW (N := N)) eη ^ e) (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gv LL ρ e m')) := by
      simp only [Bf]; rw [leading_vector_add_linked LL ρ e m hme, leading_vector_add_linked LL ρ e m' hme']
    have hQ : 0 < Q n := by
      have : (0 : ℝ) < (((n - S).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have h2 : (0 : ℝ) < (n : ℝ) ^ (S - e) := pow_pos (by exact_mod_cast (by omega : 0 < n)) _
      positivity
    have hδ : (0 : ℝ) < ((n - o : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - o)
    rw [Real.norm_eq_abs]
    simp only [f4, bd, abs_div, abs_of_pos hQ]
    rw [hBf, div_le_iff₀ hQ]
    refine le_trans hc (le_of_eq ?_)
    simp only [i0]
    field_simp
    rfl

  have hmain := ((chooseA_lim o z r).mul (((kappa_zero_tendsto_factorials o z e r).mul hf3).add hf4)).div_const P
  rw [← limit_value LL ρ z e m m' hm hm']
  have hlim_eq : 1 / ((o.factorial : ℕ) : ℝ) * (((z + e).choose e : ℝ) * e.factorial * e.factorial * T + 0) / P =
      1 / (o.factorial : ℝ) * (((z + e).choose e : ℝ) * e.factorial * e.factorial * T + 0) /
        (((LL.total).factorial : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) := by
    simp only [hP]
    rfl
  rw [← hlim_eq]
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (S + 1)] with n hn
  rw [hgam n]
  have hQ0 : (((n - S).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [f4, Q]
  rw [show S + o - e = o + (S - e) by omega, pow_add]
  field_simp
  ring
end Formalism.GM.leadingTermLemmas
