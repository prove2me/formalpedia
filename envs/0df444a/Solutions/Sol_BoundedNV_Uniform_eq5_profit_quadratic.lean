-- Prove2me | solution 1 for BoundedNV.Uniform.eq5_profit_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:23:15.972167+00:00
-- url     : https://prove2.me/submissions/dd19c842-287f-4754-9947-029878d01f13

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand

set_option autoImplicit false
open BoundedNV.Uniform
open MeasureTheory

namespace BoundedNV.Uniform

lemma bnu2_expMin_eq (a b x : ℝ) (hab : a < b) :
    expMin (unifDensity a b) x = (∫ t in a..b, min t x) / (b - a) := by
  unfold expMin unifDensity
  have h : ∀ t : ℝ, min t x * (Set.Icc a b).indicator (fun _ => 1 / (b - a)) t =
      (Set.Icc a b).indicator (fun t => min t x * (1 / (b - a))) t := by
    intro t
    by_cases ht : t ∈ Set.Icc a b <;> simp [Set.indicator, ht]
  simp_rw [h]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_mul_const]
  ring

lemma bnu2_int_min_le (a b x : ℝ) (hab : a < b) (hx : x ≤ a) :
    ∫ t in a..b, min t x = (b - a) * x := by
  have : ∫ t in a..b, min t x = ∫ t in a..b, x := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    exact min_eq_right (by linarith [ht.1])
  rw [this]; simp

lemma bnu2_int_min_ge (a b x : ℝ) (hab : a < b) (hx : b ≤ x) :
    ∫ t in a..b, min t x = (b ^ 2 - a ^ 2) / 2 := by
  have : ∫ t in a..b, min t x = ∫ t in a..b, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab.le] at ht
    exact min_eq_left (by linarith [ht.2])
  rw [this]; simp

lemma bnu2_int_min_mid (a b x : ℝ) (hax : a ≤ x) (hxb : x ≤ b) :
    ∫ t in a..b, min t x = (x ^ 2 - a ^ 2) / 2 + (b - x) * x := by
  have hc : Continuous fun t : ℝ => min t x := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in a..x, min t x = ∫ t in a..x, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    exact min_eq_left ht.2
  have e2 : ∫ t in x..b, min t x = ∫ t in x..b, x := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxb] at ht
    exact min_eq_right ht.1
  rw [e1, e2]; simp

lemma bnu2_pi_le (a b p c x : ℝ) (hab : a < b) (hx : x ≤ a) :
    nvProfit (unifDensity a b) p c x = (p - c) * x := by
  unfold nvProfit
  rw [bnu2_expMin_eq a b x hab, bnu2_int_min_le a b x hab hx]
  have : b - a ≠ 0 := by linarith
  field_simp

lemma bnu2_pi_ge (a b p c x : ℝ) (hab : a < b) (hx : b ≤ x) :
    nvProfit (unifDensity a b) p c x = p * (a + b) / 2 - c * x := by
  unfold nvProfit
  rw [bnu2_expMin_eq a b x hab, bnu2_int_min_ge a b x hab hx]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

lemma bnu2_pi_mid (a b p c x : ℝ) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    nvProfit (unifDensity a b) p c x =
      (-p / (2 * (b - a))) * x ^ 2 + (p * b / (b - a) - c) * x + (-p * a ^ 2 / (2 * (b - a))) := by
  unfold nvProfit
  rw [bnu2_expMin_eq a b x hab, bnu2_int_min_mid a b x hax hxb]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

end BoundedNV.Uniform

theorem solution (a b p c : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p) :
    ∀ x ∈ Set.Icc a b,
      nvProfit (unifDensity a b) p c x =
        (-p / (2 * (b - a))) * x ^ 2 + (p * b / (b - a) - c) * x + (-p * a ^ 2 / (2 * (b - a))) := by
  intro x hx
  exact BoundedNV.Uniform.bnu2_pi_mid a b p c x hab hx.1 hx.2
