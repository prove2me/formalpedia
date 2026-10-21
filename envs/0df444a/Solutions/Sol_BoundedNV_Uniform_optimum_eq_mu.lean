-- Prove2me | solution 1 for BoundedNV.Uniform.optimum_eq_mu
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:35:07.864986+00:00
-- url     : https://prove2.me/submissions/066775de-622c-4537-ab2d-2496831002e1

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
namespace BoundedNV.Uniform

lemma bnu2_mu_bounds (a b p c : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p) :
    a < unifMu a b p c ∧ unifMu a b p c < b := by
  have hp : 0 < p := by linarith
  have h1 : 0 < c / p := div_pos hc hp
  have h2 : c / p < 1 := (div_lt_one hp).2 hcp
  unfold unifMu
  constructor
  · nlinarith [mul_pos (sub_pos.2 h2) (sub_pos.2 hab)]
  · nlinarith [mul_pos h1 (sub_pos.2 hab)]

lemma bnu2_mid_diff (a b p c x : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hax : a ≤ x) (hxb : x ≤ b) :
    nvProfit (unifDensity a b) p c (unifMu a b p c) - nvProfit (unifDensity a b) p c x =
      p / (2 * (b - a)) * (x - unifMu a b p c) ^ 2 := by
  obtain ⟨h1, h2⟩ := bnu2_mu_bounds a b p c hab hc hcp
  rw [bnu2_pi_mid a b p c x hab hax hxb, bnu2_pi_mid a b p c _ hab h1.le h2.le]
  have hp : p ≠ 0 := by intro h; linarith
  have hba : b - a ≠ 0 := by intro h; linarith
  unfold unifMu
  field_simp
  ring

lemma bnu2_strict (a b p c x : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hx : x ≠ unifMu a b p c) :
    nvProfit (unifDensity a b) p c x < nvProfit (unifDensity a b) p c (unifMu a b p c) := by
  obtain ⟨h1, h2⟩ := bnu2_mu_bounds a b p c hab hc hcp
  have hp : 0 < p := by linarith
  have hba : 0 < b - a := by linarith
  have hpos : ∀ y, y ≠ unifMu a b p c → 0 < p / (2 * (b - a)) * (y - unifMu a b p c) ^ 2 := by
    intro y hy
    have : y - unifMu a b p c ≠ 0 := sub_ne_zero.2 hy
    positivity
  by_cases hxa : x ≤ a
  · have e1 := bnu2_pi_le a b p c x hab hxa
    have e2 := bnu2_pi_le a b p c a hab le_rfl
    have e3 := bnu2_mid_diff a b p c a hab hc hcp le_rfl hab.le
    have := hpos a (ne_of_lt h1)
    nlinarith
  · by_cases hxb : b ≤ x
    · have e1 := bnu2_pi_ge a b p c x hab hxb
      have e2 := bnu2_pi_ge a b p c b hab le_rfl
      have e3 := bnu2_mid_diff a b p c b hab hc hcp hab.le le_rfl
      have := hpos b (ne_of_gt h2)
      nlinarith
    · have := bnu2_mid_diff a b p c x hab hc hcp (le_of_not_ge hxa) (le_of_not_ge hxb)
      have := hpos x hx
      linarith

lemma bnu2_sigma_sq (a b p β : ℝ) (hab : a < b) (hp : 0 < p) (hβ : 0 < β) :
    unifSigma a b p β ^ 2 = β * (b - a) / p := by
  unfold unifSigma
  rw [Real.sq_sqrt]
  have : 0 < b - a := by linarith
  positivity

lemma bnu2_key (a b p c β : ℝ) (hab : a < b) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β) :
    ∀ t ∈ Set.Icc a b, Real.exp (nvProfit (unifDensity a b) p c t / β) =
      Real.exp (nvProfit (unifDensity a b) p c (unifMu a b p c) / β) *
        Real.exp (-(t - unifMu a b p c) ^ 2 / (2 * unifSigma a b p β ^ 2)) := by
  intro t ht
  have hp : 0 < p := by linarith
  have hba : 0 < b - a := by linarith
  rw [← Real.exp_add]
  congr 1
  have h := bnu2_mid_diff a b p c t hab hc hcp ht.1 ht.2
  rw [bnu2_sigma_sq a b p β hab hp hβ]
  have : nvProfit (unifDensity a b) p c t =
      nvProfit (unifDensity a b) p c (unifMu a b p c) - p / (2 * (b - a)) * (t - unifMu a b p c) ^ 2 := by
    linarith
  rw [this]
  field_simp
  ring

lemma bnu2_cdf (a b μ : ℝ) (hab : a < b) (h1 : a ≤ μ) (h2 : μ ≤ b) :
    demandCDF (unifDensity a b) μ = (μ - a) / (b - a) := by
  unfold demandCDF unifDensity
  rw [setIntegral_indicator measurableSet_Icc]
  have : Set.Iic μ ∩ Set.Icc a b = Set.Icc a μ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
    · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
  rw [this, setIntegral_const, Real.volume_real_Icc_of_le h1, smul_eq_mul]
  ring

end BoundedNV.Uniform

theorem solution (a b p c : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p) :
    IsMaxOn (nvProfit (unifDensity a b) p c) Set.univ (unifMu a b p c) ∧
      (∀ x, IsMaxOn (nvProfit (unifDensity a b) p c) Set.univ x → x = unifMu a b p c) ∧
      demandCDF (unifDensity a b) (unifMu a b p c) = 1 - c / p := by
  have hp : 0 < p := by linarith
  obtain ⟨h1, h2⟩ := bnu2_mu_bounds a b p c hab hc hcp
  refine ⟨?_, ?_, ?_⟩
  · refine isMaxOn_iff.2 (fun x _ => ?_)
    by_cases hx : x = unifMu a b p c
    · rw [hx]
    · exact (bnu2_strict a b p c x hab hc hcp hx).le
  · intro x hx
    by_contra hne
    have := bnu2_strict a b p c x hab hc hcp hne
    have h := isMaxOn_iff.1 hx _ (Set.mem_univ (unifMu a b p c))
    linarith
  · rw [bnu2_cdf a b _ hab h1.le h2.le]
    unfold unifMu
    have hba : b - a ≠ 0 := by intro h; linarith
    field_simp
    ring
