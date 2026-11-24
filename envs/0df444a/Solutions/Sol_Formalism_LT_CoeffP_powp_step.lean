-- Prove2me | solution 1 for Formalism.LT.CoeffP.powp_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:58.58386+00:00
-- url     : https://prove2.me/submissions/ee9dd468-eb29-43cc-8b1c-a5ba86627561

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
import Theorems.Thm_Formalism_LT_CoeffP_Bd_sum
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul_natCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.CoeffP
theorem _root_.solution {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (_hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    Bd (‖(p : K)‖ ^ (r + 1)) (A ^ p - B ^ p) := by
  have hpn : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hp1 : ‖(p : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K p

  have hexp : A ^ p - B ^ p = ∑ m ∈ Finset.range p,
      (A - B) ^ (m + 1) * B ^ (p - (m + 1)) * ((p.choose (m + 1) : ℕ) : MvPowerSeries ι K) := by
    have h := add_pow (A - B) B p
    rw [sub_add_cancel, Finset.sum_range_succ'] at h
    rw [h, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      add_sub_cancel_right]
  rw [hexp]
  refine Bd.sum (pow_nonneg hpn _) (fun m hm => ?_)
  have hm' : m < p := Finset.mem_range.mp hm
  have hDm : Bd (‖(p : K)‖ ^ (r * (m + 1))) ((A - B) ^ (m + 1)) := by
    rw [pow_mul]
    exact Bd.pow hD (pow_nonneg hpn _) (m + 1)
  have hBm : Bd 1 (B ^ (p - (m + 1))) := by
    have h := Bd.pow hB zero_le_one (p - (m + 1))
    rwa [one_pow] at h
  have hprod : Bd (‖(p : K)‖ ^ (r * (m + 1))) ((A - B) ^ (m + 1) * B ^ (p - (m + 1))) := by
    have h := Bd.mul hDm hBm (pow_nonneg hpn _) zero_le_one
    rwa [mul_one] at h
  refine Bd.mono (Bd.mul_natCast hprod (p.choose (m + 1))) ?_
  rcases Nat.lt_or_ge (m + 1) p with hlt | hge
  ·
    obtain ⟨t, ht⟩ := hp.dvd_choose_self (Nat.succ_ne_zero m) hlt
    have hc : ‖((p.choose (m + 1) : ℕ) : K)‖ ≤ ‖(p : K)‖ := by
      rw [ht, Nat.cast_mul, norm_mul]
      calc ‖(p : K)‖ * ‖(t : K)‖ ≤ ‖(p : K)‖ * 1 :=
            mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one K t) hpn
        _ = ‖(p : K)‖ := mul_one _
    have hr' : ‖(p : K)‖ ^ (r * (m + 1)) ≤ ‖(p : K)‖ ^ r :=
      pow_le_pow_of_le_one hpn hp1 (Nat.le_mul_of_pos_right r (Nat.succ_pos m))
    calc ‖((p.choose (m + 1) : ℕ) : K)‖ * ‖(p : K)‖ ^ (r * (m + 1))
        ≤ ‖(p : K)‖ * ‖(p : K)‖ ^ r := mul_le_mul hc hr' (pow_nonneg hpn _) hpn
      _ = ‖(p : K)‖ ^ (r + 1) := by ring
  ·
    have hm1 : m + 1 = p := Nat.le_antisymm (Nat.succ_le_of_lt hm') hge
    rw [hm1, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
    apply pow_le_pow_of_le_one hpn hp1
    calc r + 1 ≤ r * 2 := by omega
      _ ≤ r * p := Nat.mul_le_mul_left r hp.two_le
end Formalism.LT.CoeffP
