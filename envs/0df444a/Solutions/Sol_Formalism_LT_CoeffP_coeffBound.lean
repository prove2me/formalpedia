-- Prove2me | solution 1 for Formalism.LT.CoeffP.coeffBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:19.168554+00:00
-- url     : https://prove2.me/submissions/68b4337d-7319-4804-8632-ab2d565bf9a7

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_sigma_norm_le_one
import Theorems.Thm_Formalism_LT_CoeffP_coeff_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
universe u v
namespace Formalism.LT.CoeffP
open Formalism.G
section Ball
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Ball
private lemma norm_add_inv_mul_mul_norm_pow_succ_le_one {L : Type*} [NormedField L] [IsUltrametricDist L] (a s π : L) (k : ℕ)
    (ha : ‖a‖ ≤ 1) (hs : ‖s‖ * ‖π‖ ^ k ≤ 1) (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) :
    ‖a + π⁻¹ * s‖ * ‖π‖ ^ (k + 1) ≤ 1 := by
  have hn : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hpow0 : 0 ≤ ‖π‖ ^ (k + 1) := pow_nonneg hn.le _
  have hpow1 : ‖π‖ ^ (k + 1) ≤ 1 := by
    simpa using pow_le_pow_of_le_one hn.le hπ (Nat.zero_le (k + 1))
  refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hpow0).trans ?_
  rw [max_mul_of_nonneg _ _ hpow0]
  refine max_le ?_ ?_
  · calc ‖a‖ * ‖π‖ ^ (k + 1) ≤ 1 * 1 := mul_le_mul ha hpow1 hpow0 zero_le_one
      _ = 1 := one_mul 1
  · calc ‖π⁻¹ * s‖ * ‖π‖ ^ (k + 1) = ‖s‖ * ‖π‖ ^ k * (‖π‖⁻¹ * ‖π‖) := by
          rw [norm_mul, norm_inv, pow_succ]; ring
      _ = ‖s‖ * ‖π‖ ^ k := by rw [inv_mul_cancel₀ hn.ne', mul_one]
      _ ≤ 1 := hs
section Bd
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
end Bd
end Formalism.LT.CoeffP
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
namespace Formalism.LT.CoeffP
theorem _root_.solution : Formalism.LT.CoeffBound.{u} := by
  unfold Formalism.LT.CoeffBound
  intro K _ _ _ p q σ hset f hf0 hfe n
  have hset' : Nat.Prime p ∧ (∃ e, 0 < e ∧ q = p ^ e) ∧ ‖(p : K)‖ < 1 ∧ Formalism.G.IsFrobLift p q σ :=
    hset
  obtain ⟨hp, ⟨e, he, hqe⟩, hp1, hσ⟩ := hset'
  have hq2 : 2 ≤ q := by
    rw [hqe]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt he)
  have hq0 : q ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  have hσb : ∀ (x : K) (k : ℕ), ‖x‖ * ‖(p : K)‖ ^ k ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ k ≤ 1 := by
    intro x k hx
    have h1 : ‖x * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hx
    have h2 := sigma_norm_le_one hp1.le hσ _ h1
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    exact h2
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, dvd_zero _, ?_⟩
    have h0 : PowerSeries.coeff 0 f = 0 := by simpa using hf0
    rw [h0, norm_zero, zero_mul]
    exact zero_le_one
  · have hg : ‖PowerSeries.coeff n (f - (p : K)⁻¹ •
        (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q))‖ ≤ 1 := hfe n
    rw [coeff_split p q hq0 σ f n]
    by_cases hdiv : q ∣ n
    · have hlt : n / q < n := Nat.div_lt_self hn (by omega)
      obtain ⟨k, hk, hkb⟩ := ih (n / q) hlt
      refine ⟨k + 1, ?_, ?_⟩
      · have hnq : n = q * (n / q) := (Nat.mul_div_cancel' hdiv).symm
        rw [hnq, pow_succ']
        exact mul_dvd_mul_left q hk
      · rw [if_pos hdiv]
        exact norm_add_inv_mul_mul_norm_pow_succ_le_one _ _ _ k hg (hσb _ _ hkb) hp1.le hpK
    · refine ⟨0, by rw [pow_zero]; exact one_dvd n, ?_⟩
      rw [if_neg hdiv, mul_zero, add_zero, pow_zero, mul_one]
      exact hg
end Formalism.LT.CoeffP
