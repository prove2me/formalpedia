-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.FT_pow_coeff_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:27.576186+00:00
-- url     : https://prove2.me/submissions/1ea0bcbc-dd37-4a9f-ac81-8c9218f59309

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vchoose_le
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_nat_eq
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_pos__da61b7487fff
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_desc_le
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_sum_le_bound
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_coeff_Dop_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_insert
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (hwe : ∀ c, w c ≠ e c) (Tb B : ℕ) (hB : Nat.log p Tb ≤ B) (K : ℝ)
    (G : MvPolynomial σ ℚ_[p]) (hG : ∀ β, ‖coeff β G‖ ≤ K) (T : Finset (Fin r)) :
    ∀ b ≤ Tb, ∀ β, ‖coeff β ((FT w e T ^ b) G)‖ ≤
      K * (p : ℝ) ^ (((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hG 0)
  induction T using Finset.induction_on with
  | empty =>
    intro b _ β
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simpa using hG β
    · have : FT (p := p) w e (∅ : Finset (Fin r)) = 0 := by simp [FT]
      rw [this, zero_pow hb.ne']
      simp only [LinearMap.zero_apply, coeff_zero, norm_zero]
      exact mul_nonneg hK (zpow_pos' _).le
  | insert c T hc ih =>
    intro b hb β
    rw [FT_insert w e c T hc, (FT_commute w e (w c) (e c) T).add_pow b, LinearMap.sum_apply, coeff_sum]
    apply norm_sum_le_bound _ _ _ (mul_nonneg hK (zpow_pos' _).le)
    intro a ha
    rw [mem_range] at ha
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
      coeff_smul, nsmul_eq_mul, norm_mul, coeff_Dop_pow _ _ (hwe c), norm_mul, norm_mul]
    have h1 := ih (b - a) (by omega) (β + a • (Finsupp.single (w c) 1 + Finsupp.single (e c) 1))
    have h2 := norm_desc_le (p := p) (β (w c) + a) a
    have h3 := norm_desc_le (p := p) (β (e c) + a) a
    have hC : ‖((b.choose a : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p (b.choose a) : ℤ)) :=
      norm_nat_eq _ (Nat.choose_pos (by omega)).ne'
    have hv := vchoose_le (p := p) (k := a) hb hB
    have hfac : padicValNat p b.factorial = padicValNat p (b.choose a) + padicValNat p a.factorial +
        padicValNat p (b - a).factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial (show a ≤ b by omega),
        padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne')
          (Nat.factorial_pos _).ne',
        padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne']
    rw [hC]
    calc (p : ℝ) ^ (-(padicValNat p (b.choose a) : ℤ)) *
          (‖coeff (β + a • (Finsupp.single (w c) 1 + Finsupp.single (e c) 1)) ((FT w e T ^ (b - a)) G)‖ *
            ‖((((β (w c) + a).descFactorial a) : ℕ) : ℚ_[p])‖ * ‖((((β (e c) + a).descFactorial a) : ℕ) : ℚ_[p])‖)
        ≤ (p : ℝ) ^ (-(padicValNat p (b.choose a) : ℤ)) *
          ((K * (p : ℝ) ^ (((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p (b - a).factorial : ℤ))) *
            (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ)) * (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ))) := by
          gcongr
      _ = K * (p : ℝ) ^ ((((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p (b - a).factorial : ℤ)) +
            (-(padicValNat p a.factorial : ℤ)) + (-(padicValNat p a.factorial : ℤ)) +
            (-(padicValNat p (b.choose a) : ℤ))) := by
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
          rw [zpow_add₀ hp0, zpow_add₀ hp0, zpow_add₀ hp0]; ring
      _ ≤ K * (p : ℝ) ^ ((((insert c T).card * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          apply zpow_mono'
          rw [card_insert_of_notMem hc, hfac]
          push_cast
          linarith
end Formalism.GM.gammaIntegralityLemmas
