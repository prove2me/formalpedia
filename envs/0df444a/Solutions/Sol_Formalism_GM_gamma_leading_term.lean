-- Prove2me | solution 1 for Formalism.GM.gamma_leading_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:23.468586+00:00
-- url     : https://prove2.me/submissions/b17f4c14-6f9b-47f8-ac3b-4adb10089f1e

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_tieGam_eq
import Theorems.Thm_Formalism_GM_leadingTermLemmas_coeff_of_tendsto
import Theorems.Thm_Formalism_GM_leadingTermLemmas_real_mono
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_map
import Theorems.Thm_Formalism_GM_leadingTermLemmas_gamK_map
import Theorems.Thm_Formalism_GM_leadingTermLemmas_inMono_map
import Theorems.Thm_Formalism_GM_leadingTermLemmas_gamK_bil
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fock_init_bil
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
open Formalism Formalism.GM
open MvPolynomial Finset Filter Topology Formalism.GM.leadingTermLemmas
namespace Formalism.GM
theorem _root_.solution : M.GamLead := by
  intro p _ N r LL ρ z e f f' P hr hv hf hf' hof hof' hP
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  set D := S + o - e with hD
  set I := f.support ×ˢ f'.support with hI
  set c : (Fin (N + 1) × Fin r →₀ ℕ) × (Fin (N + 1) × Fin r →₀ ℕ) → ℚ_[p] :=
    fun i => f.coeff i.1 * f'.coeff i.2 with hc
  set γ : (Fin (N + 1) × Fin r →₀ ℕ) × (Fin (N + 1) × Fin r →₀ ℕ) → ℕ → ℚ :=
    fun i n => gamK ℚ LL ρ z n (monomial i.1 1) (monomial i.2 1) with hγ
  set Lq : (Fin (N + 1) × Fin r →₀ ℕ) × (Fin (N + 1) × Fin r →₀ ℕ) → ℚ :=
    fun i => ((e.factorial * (z + e).choose e : ℕ) : ℚ) * fk (inMono (K := ℚ) ρ e i.1) (inMono ρ e i.2) /
      (((o.factorial * S.factorial : ℕ) : ℚ) * ∏ j, ((LL.deg j).factorial : ℚ)) with hLq
  have hexp : ∀ n, M.tieGam p LL ρ z n f f' = ∑ i ∈ I, c i * algebraMap ℚ ℚ_[p] (γ i n) := by
    intro n
    rw [tieGam_eq, gamK_bil, Finset.sum_product]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
    rw [gamK_map ℚ_[p]]
  have htgt : ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
      M.fock p (M.initPart (Fin.last N, ρ) e f) (M.initPart (Fin.last N, ρ) e f') /
      (((o.factorial * S.factorial : ℕ) : ℚ_[p]) * ∏ j, ((LL.deg j).factorial : ℚ_[p])) =
      ∑ i ∈ I, c i * algebraMap ℚ ℚ_[p] (Lq i) := by
    rw [fock_init_bil, Finset.mul_sum, Finset.sum_div, Finset.sum_product]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [← inMono_map ℚ_[p], ← inMono_map ℚ_[p], fk_map]
    simp only [hLq, hc, map_div₀, map_mul, map_natCast, map_prod]
    ring
  rw [htgt, ← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp (fun ψ => ?_)
  have hψ : ∀ (a : ℚ_[p]) (q : ℚ), ψ (a * algebraMap ℚ ℚ_[p] q) = q * ψ a := by
    intro a q
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

  set Rψ : Polynomial ℚ := ∑ k ∈ range (P.natDegree + 1), Polynomial.C (ψ (P.coeff k)) * Polynomial.X ^ k with hR
  have hRcoeff : ∀ k, Rψ.coeff k = ψ (P.coeff k) := by
    intro k
    rw [hR, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have : P.natDegree < k := by simp at hk; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, map_zero]
  have hReval : ∀ q : ℚ, Rψ.eval q = ψ (P.eval (algebraMap ℚ ℚ_[p] q)) := by
    intro q
    rw [Polynomial.eval_eq_sum_range (p := P), map_sum, hR, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, hψ]
    ring
  have hRn : ∀ n : ℕ, S ≤ n → Rψ.eval (n : ℚ) = ∑ i ∈ I, γ i n * ψ (c i) := by
    intro n hn
    rw [hReval, map_natCast, ← hP n hn, hexp, map_sum]
    exact Finset.sum_congr rfl (fun i _ => hψ _ _)

  have hmem : ∀ i ∈ I, M.MultiDeg LL i.1 ∧ M.MultiDeg LL i.2 ∧ e ≤ i.1 (Fin.last N, ρ) ∧ e ≤ i.2 (Fin.last N, ρ) := by
    intro i hi
    rw [hI, Finset.mem_product] at hi
    have h1 := (MvPolynomial.mem_restrictSupport_iff _).mp hf hi.1
    have h2 := (MvPolynomial.mem_restrictSupport_iff _).mp hf' hi.2
    exact ⟨h1, h2, hof.1 _ hi.1, hof'.1 _ hi.2⟩
  set Rr : Polynomial ℝ := Rψ.map (algebraMap ℚ ℝ) with hRr
  have hlim : Tendsto (fun n : ℕ => Rr.eval (n : ℝ) / (n : ℝ) ^ D) atTop
      (𝓝 (∑ i ∈ I, (algebraMap ℚ ℝ (Lq i)) * ψ (c i))) := by
    have each : ∀ i ∈ I, Tendsto (fun n : ℕ => gamK ℝ LL ρ z n (monomial i.1 1) (monomial i.2 1) / (n : ℝ) ^ D *
        ψ (c i)) atTop (𝓝 ((algebraMap ℚ ℝ (Lq i)) * ψ (c i))) := by
      intro i hi
      obtain ⟨h1, h2, h3, h4⟩ := hmem i hi
      have := (real_mono LL ρ hr hv z e i.1 i.2 h1 h2 h3 h4).mul_const (ψ (c i) : ℝ)
      convert this using 2
      rw [hLq]
      simp only
      rw [← inMono_map ℝ ρ e i.1, ← inMono_map ℝ ρ e i.2, fk_map ℝ]
      simp only [map_div₀, map_mul, map_natCast, map_prod, eq_ratCast]
      rfl
    refine (tendsto_finsetSum I each).congr' ?_
    filter_upwards [eventually_ge_atTop S] with n hn
    rw [hRr, Polynomial.eval_natCast_map, hRn n hn, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [gamK_map ℝ]
    simp only [hγ, eq_ratCast]
    push_cast
    ring
  have hcoef := coeff_of_tendsto Rr D _ hlim
  rw [hRr, Polynomial.coeff_map, hRcoeff] at hcoef
  have hq : ψ (P.coeff D) = ∑ i ∈ I, Lq i * ψ (c i) := by
    apply (algebraMap ℚ ℝ).injective
    rw [hcoef, map_sum (algebraMap ℚ ℝ)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [eq_ratCast]
    push_cast
    ring
  rw [map_sub, hq, map_sum]
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl (fun i _ => (hψ _ _).symm)
end Formalism.GM
