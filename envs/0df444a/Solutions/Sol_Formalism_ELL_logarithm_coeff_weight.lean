-- Prove2me | solution 1 for Formalism.ELL.logarithm_coeff_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:37.660189+00:00
-- url     : https://prove2.me/submissions/c5467654-3f3e-4873-83dd-0c457a658428

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
import Theorems.Thm_Formalism_ELL_LogarithmWeight_norm_sum_mul_le
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_pow_le
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_pow_self
import Theorems.Thm_Formalism_ELL_LogarithmWeight_coeff_subst_eq_sum
import Theorems.Thm_Formalism_ELL_LogarithmWeight_log_comp_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution : Formalism.ELL.LogWeight := by
  intro K _ _ _ p q hp hp0 hp1 hq F e l he heI he1 he0 hl n hn
  set P : K := (p : K) with hPdef
  have hP0 : P ≠ 0 := norm_pos_iff.mp hp0
  have hle := Formalism.ELL.LogarithmWeight.log_comp_hom P hP0 he he1 hl
  have hq1 : (0:ℝ) < (q:ℝ) - 1 := by
    have : (2:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set c : ℝ := ‖P‖ ^ (1 / ((q:ℝ) - 1)) with hc
  have cpos : 0 < c := Real.rpow_pos_of_pos hp0 _
  have cle : c ≤ 1 := Real.rpow_le_one (norm_nonneg _) hp1.le (div_nonneg zero_le_one hq1.le)
  have cpow : c ^ (q - 1) = ‖P‖ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_one, one_div, inv_mul_cancel₀ hq1.ne', Real.rpow_one]
  have cq : c ^ q = ‖P‖ * c := by
    rw [← cpow, ← pow_succ]
    congr 1
    omega
  have heB : ∀ d, ‖coeff d e‖ * c ^ d ≤ c ^ q := by
    intro d
    rcases Nat.lt_or_ge d q with hd | hd
    · rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with rfl | rfl | hd2
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, he.1]
        simp only [norm_zero, zero_mul]
        positivity
      · rw [he1, pow_one, cq]
      · rw [he0 d hd2 hd]
        simp only [norm_zero, zero_mul]
        positivity
    · calc ‖coeff d e‖ * c ^ d ≤ 1 * c ^ d := by
            gcongr
            exact heI d
        _ = c ^ d := one_mul _
        _ ≤ c ^ q := pow_le_pow_of_le_one cpos.le cle hd
  have hpow : ∀ m k, ‖coeff k (e ^ m)‖ * c ^ k ≤ (c ^ q) ^ m :=
    Formalism.ELL.LogarithmWeight.coeff_pow_le cpos (by positivity) heB
  have hdiff : ∀ k, 2 ≤ k → ‖P‖ ≤ ‖P - P ^ k‖ := by
    intro k hk
    have hlt : ‖P ^ k‖ < ‖P‖ := by
      rw [norm_pow]
      exact pow_lt_self_of_lt_one₀ hp0 hp1 (by omega)
    have := IsUltrametricDist.norm_add_le_max (P - P ^ k) (P ^ k)
    rw [sub_add_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
  have main : ∀ k, 1 ≤ k → ‖coeff k l‖ * c ^ k ≤ c := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · rw [hl.2.1]
      simp
    have hcoef := congrArg (coeff k) hle
    rw [Formalism.ELL.LogarithmWeight.coeff_subst_eq_sum he.1, Finset.sum_range_succ,
      Formalism.ELL.LogarithmWeight.coeff_pow_self he.1, he1, map_smul, smul_eq_mul] at hcoef
    have hS : coeff k l * (P - P ^ k) = ∑ m ∈ Finset.range k, coeff m l * coeff k (e ^ m) := by
      rw [mul_sub, mul_comm (coeff k l) P, ← hcoef]
      ring
    have hSb : ‖∑ m ∈ Finset.range k, coeff m l * coeff k (e ^ m)‖ * c ^ k ≤ c ^ q := by
      apply Formalism.ELL.LogarithmWeight.norm_sum_mul_le _ _ (pow_pos cpos k) (by positivity)
      intro m hm
      rw [Finset.mem_range] at hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl.1]
        simp only [zero_mul, norm_zero]
        positivity
      · have h1 := ih m hm hm0
        have h2 := hpow m k
        rw [norm_mul]
        have hqm : q + m ≤ 1 + q * m := by nlinarith
        have key : ‖coeff m l‖ * ‖coeff k (e ^ m)‖ * c ^ k * c ^ m ≤ c ^ q * c ^ m := by
          calc ‖coeff m l‖ * ‖coeff k (e ^ m)‖ * c ^ k * c ^ m
              = (‖coeff m l‖ * c ^ m) * (‖coeff k (e ^ m)‖ * c ^ k) := by ring
            _ ≤ c * (c ^ q) ^ m := mul_le_mul h1 h2 (by positivity) cpos.le
            _ = c ^ (1 + q * m) := by rw [← pow_mul, ← pow_succ', add_comm]
            _ ≤ c ^ (q + m) := pow_le_pow_of_le_one cpos.le cle hqm
            _ = c ^ q * c ^ m := pow_add _ _ _
        exact le_of_mul_le_mul_right key (pow_pos cpos m)
    have : ‖coeff k l‖ * c ^ k * ‖P‖ ≤ c * ‖P‖ := by
      calc ‖coeff k l‖ * c ^ k * ‖P‖ ≤ ‖coeff k l‖ * c ^ k * ‖P - P ^ k‖ := by
            gcongr
            exact hdiff k hk2
        _ = ‖coeff k l * (P - P ^ k)‖ * c ^ k := by rw [norm_mul]; ring
        _ ≤ c ^ q := by rw [hS]; exact hSb
        _ = c * ‖P‖ := by rw [cq, mul_comm]
    exact le_of_mul_le_mul_right this hp0
  have hm := main n hn
  have hcn : 0 < c ^ n := pow_pos cpos n
  have hfin : ‖coeff n l‖ ≤ c / c ^ n := by
    rw [le_div_iff₀ hcn]
    exact hm
  refine hfin.trans (le_of_eq ?_)
  rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_sub hp0]
  congr 1
  ring
end Formalism.ELL
