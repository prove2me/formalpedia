-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.per_rowX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:36:27.197373+00:00
-- url     : https://prove2.me/submissions/07d40bf9-8f94-4c37-9f75-72886e6e1240

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMXB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_NatLogLeOfLe
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_sum
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
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


section
namespace Formalism.InvariantFactorPaths.MC
open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
private lemma neg_logb_norm_natCast_eq_padicValNat (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    -Real.logb p ‖(n : ℚ_[p])‖ = (padicValNat p n : ℝ) := by
  have h0 : ((n : ℚ) : ℚ_[p]) = (n : ℚ_[p]) := by push_cast; rfl
  have h1 : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
    rw [← h0, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
      padicValRat.of_nat]
    push_cast <;> simp [padicValRat.of_nat]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [h1, ← Real.rpow_intCast, Real.logb_rpow (by positivity) hp1.ne']
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
private lemma digits_sum_le_sub_one_mul_log_add_one (p : ℕ) [hp : Fact p.Prime] (n Xb : ℕ) (hn : n ≤ Xb) :
    ((p.digits n).sum : ℝ) ≤ ((p : ℝ) - 1) * ((Nat.log p Xb : ℝ) + 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by positivity)
  · have hlen := Nat.digits_len p n hp.out.one_lt hpos.ne'
    have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
      have := List.sum_le_card_nsmul (p.digits n) (p - 1)
        (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp.out.one_lt hx))
      simpa [smul_eq_mul] using this
    rw [hlen] at hsum
    have hlog : Nat.log p n ≤ Nat.log p Xb := Nat.log_mono_right hn
    have h2 : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
      have h3 := (Nat.cast_le (α := ℝ)).mpr hsum
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.out.one_lt.le, Nat.cast_one] at h3
      exact h3
    have hl : (Nat.log p n : ℝ) ≤ Nat.log p Xb := by exact_mod_cast hlog
    nlinarith
end Formalism.InvariantFactorPaths.MC
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC
open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.MC
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (Xb S o z e Mm : ℕ) (κ κ4 lgv : ℝ)
    (heo : e ≤ o) (ho : o ≤ Xb) (hS : S ≤ Xb) (hz : z + o ≤ Xb) (hL : (Nat.log p Xb : ℝ) + 1 ≤ lgv)
    (hκ0 : 0 ≤ κ) (hM : Mm = ⌈κ⌉₊) :
    -Real.logb p ‖betaT p Mm z o S e‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ4 ≤
      κ + 3 * lgv + κ4 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hq : 0 < (p : ℝ) - 1 := by linarith
  have hA : p ^ Mm * (e.factorial * (z + e).choose e) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.out.ne_zero)
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne')
  have hB : o.factorial * S.factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hβ : betaT p Mm z o S e = ((p ^ Mm * (e.factorial * (z + e).choose e) : ℕ) : ℚ_[p]) /
      ((o.factorial * S.factorial : ℕ) : ℚ_[p]) := by
    simp only [betaT]; push_cast; ring
  have hA' : ‖((p ^ Mm * (e.factorial * (z + e).choose e) : ℕ) : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast hA)
  have hB' : ‖((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast hB)
  rw [hβ, norm_div, Real.logb_div hA' hB']
  have e1 := neg_logb_norm_natCast_eq_padicValNat p _ hA
  have e2 := neg_logb_norm_natCast_eq_padicValNat p _ hB
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero)
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'),
    padicValNat.prime_pow, padicValNat.mul (Nat.factorial_ne_zero _)
      (Nat.choose_pos (Nat.le_add_left e z)).ne'] at e1
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at e2
  simp only [Nat.cast_add] at e1 e2
  have hC : (padicValNat p ((z + e).choose e) : ℝ) ≤ Nat.log p Xb := by
    have h := @Nat.factorization_choose_le_log p (z + e) e
    rw [Nat.factorization_def _ hp.out] at h
    exact_mod_cast h.trans (Nat.log_mono_right (by omega))
  have L : ∀ n : ℕ, ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = n - ((p.digits n).sum : ℝ) := by
    intro n
    have h := sub_one_mul_padicValNat_factorial (p := p) n
    have h' : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) = ((n - (p.digits n).sum : ℕ) : ℝ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_sub (Nat.digit_sum_le p n), Nat.cast_sub hp.out.one_lt.le] at h'
    simpa using h'
  have dso := digits_sum_le_sub_one_mul_log_add_one p o Xb ho
  have dsS := digits_sum_le_sub_one_mul_log_add_one p S Xb hS
  have dse : (0 : ℝ) ≤ ((p.digits e).sum : ℝ) := by positivity
  have Le := L e
  have Lo := L o
  have LS := L S
  have hsub : ((S + o - e : ℕ) : ℝ) = (S : ℝ) + o - e := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlv : ((p : ℝ) - 1) * ((Nat.log p Xb : ℝ) + 1) ≤ ((p : ℝ) - 1) * lgv :=
    mul_le_mul_of_nonneg_left hL hq.le
  have hdiv : ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) ≤
      2 * lgv - ((padicValNat p e.factorial : ℝ) - padicValNat p o.factorial - padicValNat p S.factorial) := by
    rw [div_le_iff₀ hq, hsub]
    nlinarith
  have hceil : (Mm : ℝ) < κ + 1 := by rw [hM]; exact Nat.ceil_lt_add_one hκ0
  have hL' : (Nat.log p Xb : ℝ) ≤ lgv - 1 := by linarith
  linarith
end Formalism.InvariantFactorPaths.MC
