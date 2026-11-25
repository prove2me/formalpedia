-- Prove2me | solution 1 for FrontierMathLean.three_term_power_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:55:51.18434+00:00
-- url     : https://prove2.me/submissions/4c507477-07cb-4f99-9110-e88a0508af9b

import Definitions.Def_FrontierMathLean_AbstractInequality
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Theorems.Thm_FrontierMathLean_three_term_ratio_inequality

set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {a b c u v : ℝ} {k : ℕ}
    (ha : 0 < a) (hu : 0 < u)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) (hvc : v ≤ c) :
    5 + 2 * ((v / u) ^ k + ((v / u) ^ k)⁻¹) ≤
      (a ^ k + b ^ k + c ^ k) *
        ((a ^ k)⁻¹ + (b ^ k)⁻¹ + (c ^ k)⁻¹) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hb : 0 < b := lt_of_lt_of_le hv hvb
  have hc : 0 < c := lt_of_lt_of_le hv hvc
  have hA : 0 < a ^ k := pow_pos ha k
  have hB : 0 < b ^ k := pow_pos hb k
  have hC : 0 < c ^ k := pow_pos hc k
  have huv_ratio : 1 ≤ v / u := (one_le_div hu).2 huv
  have hratio_base_B : v / u ≤ b / a := by
    apply (div_le_div_iff₀ hu ha).2
    calc
      v * a ≤ b * a := mul_le_mul_of_nonneg_right hvb ha.le
      _ ≤ b * u := mul_le_mul_of_nonneg_left hau hb.le
  have hratio_base_C : v / u ≤ c / a := by
    apply (div_le_div_iff₀ hu ha).2
    calc
      v * a ≤ c * a := mul_le_mul_of_nonneg_right hvc ha.le
      _ ≤ c * u := mul_le_mul_of_nonneg_left hau hc.le
  have hratioB : (v / u) ^ k ≤ b ^ k / a ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_pos hv hu).le hratio_base_B k
  have hratioC : (v / u) ^ k ≤ c ^ k / a ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_pos hv hu).le hratio_base_C k
  exact three_term_ratio_inequality hA hB hC
    (one_le_pow₀ huv_ratio) hratioB hratioC
end FrontierMathLean
